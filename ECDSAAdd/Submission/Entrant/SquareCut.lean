import ECDSAAdd.Submission.Entrant.LeaveReductions

open ECDSAAdd ECDSAAdd.Secp256k1 ECDSAAdd.Entrant ECDSAAdd.Arithmetic

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.InteriorCarry
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def label (r : Bool × Option Wire) (s : BasisState) : Bool := r.1 ^^ r.2.elim false s

def affine (r : Bool × Option Wire) (a b c : Wire) : Program :=
  [.CX a c, .CX b c] ++ r.2.elim [] (fun q => [.CX q c]) ++ (if r.1 then [.X c] else [])

def add (r : Bool × Option Wire) : Nat → List Wire → List Wire → List Wire → Wire → Program
  | 0, a::a'::as, b::b'::bs, c::cs, ci =>
    affine r a' b' c ++ addInPlace (a'::as) (b'::bs) cs c ++ eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | k+1, a::a'::as, b::b'::bs, c::cs, ci =>
    majority a b ci c ++ add r k (a'::as) (b'::bs) cs c ++ eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | _, x,y,cs,ci => addInPlace x y cs ci

def OK (r : Bool × Option Wire) : Nat → List Wire → List Wire → Bool → BasisState → Prop
  | 0, a::a'::as, b::b'::bs, ci, s => carryBit (s a) (s b) ci = (s a' ^^ s b' ^^ label r s)
  | k+1, a::a'::as, b::b'::bs, ci, s => OK r k (a'::as) (b'::bs) (carryBit (s a) (s b) ci) s
  | _,_,_,_,_ => True

theorem affine_mc (r : Bool × Option Wire) (a b c : Wire) : measurementCount (affine r a b c)=0 := by
  rcases r with ⟨b,r⟩; cases b <;> cases r <;> rfl

theorem affine_tc (r : Bool × Option Wire) (a b c : Wire) : toffoliCount (affine r a b c)=0 := by
  rcases r with ⟨b,r⟩; cases b <;> cases r <;> rfl

theorem mc (r : Bool × Option Wire) (k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (add r k x y cs ci)=measurementCount (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp [add,addInPlace,measurementCount_append,affine_mc,majority,measurementCount]
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp [add,addInPlace,measurementCount_append,ih]

theorem affine_run (r : Bool × Option Wire) (a b c : Wire) (s : State)
    (ha : a≠c) (hb : b≠c) (hr : ∀ q∈r.2,q≠c) :
    run (affine r a b c) [] s =
      ⟨s.phase, writeBit s.basis c (s.basis c ^^ (s.basis a ^^ s.basis b ^^ label r s.basis))⟩ := by
  rcases r with ⟨neg,r⟩
  cases r with
  | none =>
    cases neg <;>
      simp only [affine,Option.elim_none,List.append_nil,List.nil_append,Bool.false_eq_true,if_false,if_true,
        Prod.fst,Prod.snd,List.cons_append,run,label,Option.elim_none] <;>
      apply State.extensionality
    all_goals first | rfl | (funext q; by_cases hq:q=c <;> simp [writeBit,Function.update,hq,ha,hb,Bool.xor_assoc])
  | some r =>
    have hrc : r≠c := hr r (by simp)
    cases neg <;>
      simp only [affine,Option.elim_some,List.append_nil,List.nil_append,Bool.false_eq_true,if_false,if_true,
        Prod.fst,Prod.snd,List.cons_append,run,label,Option.elim_some] <;>
      apply State.extensionality
    all_goals first | rfl | (funext q; by_cases hq:q=c <;> simp [writeBit,Function.update,hq,ha,hb,hrc,Bool.xor_assoc])


theorem OK_congr (r : Bool × Option Wire) (k : Nat) (x y : List Wire) (ci : Bool) (s t : BasisState)
    (h : ∀q∈x++y,s q=t q) (hr : label r s=label r t) :
    OK r k x y ci s ↔ OK r k x y ci t := by
  induction k generalizing x y ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> try rfl
    simp only [OK,h a (by simp),h b (by simp),h a' (by simp),h b' (by simp),hr]
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> try rfl
    simp only [OK,h a (by simp),h b (by simp)]
    exact ih _ _ _ (fun q hq => h q (by simp at hq ⊢; tauto))

theorem eq (r : Bool × Option Wire) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hr : ∀q∈r.2,q∉cs)
    (hok : OK r k x y (s.basis ci) s.basis) :
    run (add r k x y cs ci) m s = run (addInPlace x y cs ci) m s := by
  induction k generalizing x y cs ci s m with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try rfl
    have hcnt := List.nodup_iff_count.mp hn
    have h4 : [a,b,ci,c].Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
    have hac : a' ≠ c := by
      intro e; have := hcnt c; subst e
      simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at this; omega
    have hbc : b' ≠ c := by
      intro e; have := hcnt c; subst e
      simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at this; omega
    have hrc : ∀q∈r.2,q≠c := by intro q hq e; subst e; exact hr q hq (by simp)
    have hmid : run (affine r a' b' c) [] s=run (majority a b ci c) [] s := by
      rw [affine_run r _ _ c s hac hbc hrc,majority_correct _ _ _ _ h4]
      congr 2
      exact congrArg (fun z => s.basis c ^^ z) hok.symm
    simp only [add,addInPlace,List.append_assoc]
    exact TopCarry.run_head_congr _ _ _ m s (affine_mc _ _ _ _) (by rfl) hmid
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try rfl
    have hcnt := List.nodup_iff_count.mp hn
    have h4 : [a,b,ci,c].Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    have cn := (List.nodup_cons.mp hnd').1
    have notc (q : Wire) (hq : q∈(a'::as)++(b'::bs)) : q≠c := by
      intro e; subst e; exact cn (List.mem_append_left _ hq)
    have hc0 := hclean c (by simp)
    let u : State := ⟨s.phase,writeBit s.basis c (carryBit (s.basis a) (s.basis b) (s.basis ci))⟩
    have hmaj : run (majority a b ci c) [] s=u := by
      rw [majority_correct _ _ _ _ h4]; simp [u,hc0]
    have uc : u.basis c=carryBit (s.basis a) (s.basis b) (s.basis ci) := by simp [u,writeBit]
    have uk (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,Function.update,hq]
    have hr' : ∀q∈r.2,q∉cs := fun q hq h => hr q hq (by simp [h])
    have hlabel : label r u.basis=label r s.basis := by
      unfold label
      congr 1
      cases he : r.2 with
      | none => rfl
      | some q =>
        apply uk
        intro e; subst e; exact hr q (by rw [he]; simp) (by simp)
    have okIn : OK r k (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,OK_congr r k _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq)) hlabel]
      exact hok
    have cleanIn : ∀q∈cs,u.basis q=false := by
      intro q hq
      have hqc : q≠c := by intro e; subst e; exact cn (List.mem_append_right _ hq)
      rw [uk q hqc]; exact hclean q (by simp [hq])
    simp only [add,addInPlace]
    have he := TopCarry.run_mid_congr (majority a b ci c) (add r k (a'::as) (b'::bs) cs c)
      (addInPlace (a'::as) (b'::bs) cs c) (eraseCarry a b ci c ++ [.CX a b,.CX ci b]) m s
      (by rfl) (mc r k _ _ cs c) (fun record => by
        rw [hmaj]
        exact ih _ _ cs c hnd' u record cleanIn hr' okIn)
    simpa only [List.append_assoc] using he


theorem tc (r : Bool × Option Wire) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) (hk : k+2≤y.length) :
    toffoliCount (add r k x y cs ci)+1=toffoliCount (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    simp only [add,addInPlace,toffoliCount_append,affine_tc,majority,toffoliCount]
    omega
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    have h := ih (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [add,addInPlace,toffoliCount_append]
    omega

private theorem number_step (A B C : Bool) (X Y : Nat) :
    ((A.toNat+2*X)+(B.toNat+2*Y)+C.toNat)/2 = X+Y+(carryBit A B C).toNat := by
  have h := fullAdder_bit_value A B C
  have hs : (sumBit A B C).toNat<2 := by cases sumBit A B C <;> decide
  omega

private theorem base_bit (A A' B B' C R : Bool) (X Y : Nat)
    (h : (((A.toNat+2*(A'.toNat+2*X))+(B.toNat+2*(B'.toNat+2*Y))+C.toNat)/2%2=1) ↔ R=true) :
    carryBit A B C = (A' ^^ B' ^^ R) := by
  cases A <;> cases A' <;> cases B <;> cases B' <;> cases C <;> cases R <;> simp_all [carryBit] <;> omega

theorem of_sum_bit (r : Bool × Option Wire) (k : Nat) (x y : List Wire) (ci : Bool) (s : BasisState)
    (h : ((regValue x s+regValue y s+ci.toNat)/2^(k+1)%2=1) ↔ label r s=true) :
    OK r k x y ci s := by
  induction k generalizing x y ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> try trivial
    exact base_bit (s a) (s a') (s b) (s b') ci (label r s) (regValue as s) (regValue bs s) (by simpa only [TopCarry.regValue_cons',Nat.zero_add,pow_one] using h)
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> try trivial
    apply ih
    have hs := number_step (s a) (s b) ci (regValue (a'::as) s) (regValue (b'::bs) s)
    change ((regValue (a'::as) s+regValue (b'::bs) s+(carryBit (s a) (s b) ci).toNat)/2^(k+1)%2=1) ↔ _
    rw [← hs, Nat.div_div_eq_div_mul, ← pow_succ']
    simpa only [TopCarry.regValue_cons'] using h

def pair (r : Bool × Option Wire) (v : Bool) : Nat → List Wire → List Wire → List Wire → Wire → Program
  | 0,a::a'::as,b::b'::bs,c::cs,ci =>
      affine r a' b' c ++ add (v,none) 0 (a'::as) (b'::bs) cs c ++ eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | k+1,a::a'::as,b::b'::bs,c::cs,ci =>
      majority a b ci c ++ pair r v k (a'::as) (b'::bs) cs c ++ eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | _,x,y,cs,ci => addInPlace x y cs ci

theorem pair_mc (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (pair r v k x y cs ci)=measurementCount (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp [pair,addInPlace,measurementCount_append,affine_mc,mc,majority,measurementCount]
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp [pair,addInPlace,measurementCount_append,ih]

theorem pair_tc (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) (hk : k+3≤y.length) :
    toffoliCount (pair r v k x y cs ci)+2=toffoliCount (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    have h := tc (v,none) 0 (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [pair,addInPlace,toffoliCount_append,affine_tc,majority,toffoliCount]
    omega
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    have h := ih (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [pair,addInPlace,toffoliCount_append]
    omega

theorem pair_eq (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hr : ∀q∈r.2,q∉cs)
    (hok : OK r k x y (s.basis ci) s.basis) (hok2 : OK (v,none) (k+1) x y (s.basis ci) s.basis) :
    run (pair r v k x y cs ci) m s = run (addInPlace x y cs ci) m s := by
  induction k generalizing x y cs ci s m with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try rfl
    have hcnt := List.nodup_iff_count.mp hn
    have h4 : [a,b,ci,c].Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    have cn := (List.nodup_cons.mp hnd').1
    have notc (q : Wire) (hq : q∈(a'::as)++(b'::bs)) : q≠c := by
      intro e; subst e; exact cn (List.mem_append_left _ hq)
    have hc0 := hclean c (by simp)
    let u : State := ⟨s.phase,writeBit s.basis c (carryBit (s.basis a) (s.basis b) (s.basis ci))⟩
    have hmaj : run (majority a b ci c) [] s=u := by
      rw [majority_correct _ _ _ _ h4]; simp [u,hc0]
    have haff : run (affine r a' b' c) [] s=u := by
      rw [affine_run r _ _ c s (notc a' (by simp)) (notc b' (by simp))
        (by intro q hq e; subst e; exact hr q hq (by simp))]
      simp only [u]
      congr 2
      simpa only [hc0,Bool.false_xor] using hok.symm
    have uc : u.basis c=carryBit (s.basis a) (s.basis b) (s.basis ci) := by simp [u,writeBit]
    have uk (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,Function.update,hq]
    have okIn2 : OK (v,none) 0 (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,OK_congr (v,none) 0 _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq)) rfl]
      exact hok2
    have cleanIn : ∀q∈cs,u.basis q=false := by
      intro q hq
      have hqc : q≠c := by intro e; subst e; exact cn (List.mem_append_right _ hq)
      rw [uk q hqc]; exact hclean q (by simp [hq])
    simp only [pair,addInPlace,List.append_assoc]
    rw [run_append (affine _ _ _ _),run_append (majority _ _ _ _),affine_mc,
      show measurementCount (majority a b ci c)=0 from rfl,List.take_zero,List.drop_zero,haff,hmaj]
    rw [run_append,run_append,mc,eq (v,none) 0 _ _ cs c hnd' u _ cleanIn (by simp) okIn2]
    simp only [run_append]
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try rfl
    have hcnt := List.nodup_iff_count.mp hn
    have h4 : [a,b,ci,c].Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    have cn := (List.nodup_cons.mp hnd').1
    have notc (q : Wire) (hq : q∈(a'::as)++(b'::bs)) : q≠c := by
      intro e; subst e; exact cn (List.mem_append_left _ hq)
    have hc0 := hclean c (by simp)
    let u : State := ⟨s.phase,writeBit s.basis c (carryBit (s.basis a) (s.basis b) (s.basis ci))⟩
    have hmaj : run (majority a b ci c) [] s=u := by
      rw [majority_correct _ _ _ _ h4]; simp [u,hc0]
    have uc : u.basis c=carryBit (s.basis a) (s.basis b) (s.basis ci) := by simp [u,writeBit]
    have uk (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,Function.update,hq]
    have hr' : ∀q∈r.2,q∉cs := fun q hq h => hr q hq (by simp [h])
    have hlabel : label r u.basis=label r s.basis := by
      unfold label
      congr 1
      cases he : r.2 with
      | none => rfl
      | some q =>
        apply uk
        intro e; subst e; exact hr q (by rw [he]; simp) (by simp)
    have okIn : OK r k (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,OK_congr r k _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq)) hlabel]
      exact hok
    have okIn2 : OK (v,none) (k+1) (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,OK_congr (v,none) (k+1) _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq)) rfl]
      exact hok2
    have cleanIn : ∀q∈cs,u.basis q=false := by
      intro q hq
      have hqc : q≠c := by intro e; subst e; exact cn (List.mem_append_right _ hq)
      rw [uk q hqc]; exact hclean q (by simp [hq])
    simp only [pair,addInPlace]
    have he := TopCarry.run_mid_congr (majority a b ci c) (pair r v k (a'::as) (b'::bs) cs c)
      (addInPlace (a'::as) (b'::bs) cs c) (eraseCarry a b ci c ++ [.CX a b,.CX ci b]) m s
      (by rfl) (pair_mc r v k _ _ cs c) (fun record => by
        rw [hmaj]
        exact ih _ _ cs c hnd' u record cleanIn hr' okIn okIn2)
    simpa only [List.append_assoc] using he


def low0 (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire) : Program :=
  pair r v k x.tail y.tail cs.tail ci ++ [.measureX (cs.headD 0) [] []]

def lowNC (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire) : Program :=
  low0 r v k x y cs ci ++ [.CX (x.headD 0) (y.headD 0),.CX ci (y.headD 0)]

def sub (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire) : Program :=
  notRegister y ++ lowNC r v k x y cs ci ++ notRegister y

theorem low0_mc (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (low0 r v k x y cs ci)=measurementCount (LowZero.addLow0 x y cs ci) := by
  simp only [low0,LowZero.addLow0,measurementCount_append,pair_mc]

theorem lowNC_mc (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (lowNC r v k x y cs ci)=measurementCount (LowZero.addLowNC x y cs ci) := by
  simp only [lowNC,LowZero.addLowNC,LowZero.addLow0,measurementCount_append,low0_mc]

theorem sub_mc (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (sub r v k x y cs ci)=measurementCount (LowZero.subLowNC x y cs ci) := by
  simp only [sub,LowZero.subLowNC,measurementCount_append,lowNC_mc]

theorem low0_eq (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,s.basis q=false) (hr : ∀q∈r.2,q∉cs.tail)
    (hok : OK r k x.tail y.tail (s.basis ci) s.basis)
    (hok2 : OK (v,none) (k+1) x.tail y.tail (s.basis ci) s.basis) :
    run (low0 r v k x y cs ci) m s=run (LowZero.addLow0 x y cs ci) m s := by
  simp only [low0,LowZero.addLow0,run_append,pair_mc,pair_eq r v k _ _ _ ci hn s _ hclean hr hok hok2]

theorem lowNC_eq (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,s.basis q=false) (hr : ∀q∈r.2,q∉cs.tail)
    (hok : OK r k x.tail y.tail (s.basis ci) s.basis)
    (hok2 : OK (v,none) (k+1) x.tail y.tail (s.basis ci) s.basis) :
    run (lowNC r v k x y cs ci) m s=run (LowZero.addLowNC x y cs ci) m s := by
  change run (low0 r v k x y cs ci ++ _) m s=run (LowZero.addLow0 x y cs ci ++ _) m s
  rw [run_append,run_append,low0_mc,low0_eq r v k _ _ _ ci hn s _ hclean hr hok hok2]

theorem sub_eq (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,(run (notRegister y) [] s).basis q=false) (hr : ∀q∈r.2,q∉cs.tail)
    (hok : OK r k x.tail y.tail ((run (notRegister y) [] s).basis ci) (run (notRegister y) [] s).basis)
    (hok2 : OK (v,none) (k+1) x.tail y.tail ((run (notRegister y) [] s).basis ci) (run (notRegister y) [] s).basis) :
    run (sub r v k x y cs ci) m s=run (LowZero.subLowNC x y cs ci) m s := by
  have he := TopCarry.run_mid_congr (notRegister y) (lowNC r v k x y cs ci)
    (LowZero.addLowNC x y cs ci) (notRegister y) m s (notRegister_counts y).2
    (lowNC_mc r v k x y cs ci) (fun record => lowNC_eq r v k x y cs ci hn _ record hclean hr hok hok2)
  exact he

theorem low_counts (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.tail.length=y.tail.length) (hc : cs.tail.length+1=y.tail.length) (hk : k+3≤y.tail.length) :
    toffoliCount (low0 r v k x y cs ci)+2=toffoliCount (LowZero.addLow0 x y cs ci) ∧
    toffoliCount (lowNC r v k x y cs ci)+2=toffoliCount (LowZero.addLowNC x y cs ci) ∧
    toffoliCount (sub r v k x y cs ci)+2=toffoliCount (LowZero.subLowNC x y cs ci) := by
  have h := pair_tc r v k x.tail y.tail cs.tail ci hx hc hk
  simp only [low0,lowNC,sub,LowZero.addLow0,LowZero.addLowNC,LowZero.subLowNC,toffoliCount_append]
  omega

theorem affine_physical (r : Bool × Option Wire) (a b c : Wire)
    (ha : a≠c) (hb : b≠c) (hr : ∀q∈r.2,q≠c) : GatePhysical (affine r a b c) := by
  rcases r with ⟨v,r⟩
  cases r with
  | none =>
    cases v <;> intro i hi <;> simp [affine] at hi <;> rcases hi with rfl|rfl|rfl <;>
      simp [RecordedQuantum.PhysicalInstr,ProperGate,ha,hb]
  | some r =>
    have hrc : r≠c := hr r (by simp)
    cases v <;> intro i hi <;> simp [affine] at hi <;> rcases hi with rfl|rfl|rfl|rfl <;>
      simp [RecordedQuantum.PhysicalInstr,ProperGate,ha,hb,hrc]

theorem add_physical (r : Bool × Option Wire) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (hr : ∀q∈r.2,q∉cs)
    (hp : GatePhysical (addInPlace x y cs ci)) : GatePhysical (add r k x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact hp
    have hcnt := List.nodup_iff_count.mp hn
    have hac : a'≠c := by intro e; have := hcnt c; subst e; simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at this; omega
    have hbc : b'≠c := by intro e; have := hcnt c; subst e; simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at this; omega
    simp only [add,addInPlace,gatePhysical_append] at hp ⊢
    exact ⟨⟨⟨affine_physical r _ _ c hac hbc (fun q hq e => hr q hq (by simp [e])),hp.1.1.2⟩,hp.1.2⟩,hp.2⟩
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact hp
    have hcnt := List.nodup_iff_count.mp hn
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    simp only [add,addInPlace,gatePhysical_append] at hp ⊢
    exact ⟨⟨⟨hp.1.1.1,ih _ _ cs c hnd' (fun q hq h => hr q hq (by simp [h])) hp.1.1.2⟩,hp.1.2⟩,hp.2⟩

theorem pair_physical (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (hr : ∀q∈r.2,q∉cs)
    (hp : GatePhysical (addInPlace x y cs ci)) : GatePhysical (pair r v k x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact hp
    have hcnt := List.nodup_iff_count.mp hn
    have hac : a'≠c := by intro e; have := hcnt c; subst e; simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at this; omega
    have hbc : b'≠c := by intro e; have := hcnt c; subst e; simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at this; omega
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    simp only [pair,addInPlace,gatePhysical_append] at hp ⊢
    exact ⟨⟨⟨affine_physical r _ _ c hac hbc (fun q hq e => hr q hq (by simp [e])),
      add_physical (v,none) 0 _ _ cs c hnd' (by simp) hp.1.1.2⟩,hp.1.2⟩,hp.2⟩
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact hp
    have hcnt := List.nodup_iff_count.mp hn
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    simp only [pair,addInPlace,gatePhysical_append] at hp ⊢
    exact ⟨⟨⟨hp.1.1.1,ih _ _ cs c hnd' (fun q hq h => hr q hq (by simp [h])) hp.1.1.2⟩,hp.1.2⟩,hp.2⟩

theorem of_sum_testBit (r : Bool × Option Wire) (k : Nat) (x y : List Wire) (ci : Bool) (s : BasisState)
    (h : (regValue x s+regValue y s+ci.toNat).testBit (k+1)=label r s) :
    OK r k x y ci s := by
  apply of_sum_bit
  rw [Nat.testBit_eq_decide_div_mod_eq] at h
  exact of_decide_eq_true (by rw [← h]; simp)

theorem sub_tail_bit (X Y n j : Nat) (hn : 1≤n) (hj : j+1<n)
    (hX : X%2=0) (hXY : X≤Y) (hY : Y<2^n) :
    (X/2+(2^(n-1)-1-Y/2)).testBit j = !(Y-X).testBit (j+1) := by
  have hp : 2^n=2*2^(n-1) := by rw [← pow_succ']; congr 1; omega
  have hYD : Y/2<2^(n-1) := by omega
  have hD : (Y-X)/2<2^(n-1) := by omega
  have hhalf : (Y-X)/2=Y/2-X/2 := by omega
  have he : X/2+(2^(n-1)-1-Y/2)=2^(n-1)-((Y-X)/2+1) := by omega
  rw [he,Nat.testBit_two_pow_sub_succ hD,show decide (j<n-1)=true from decide_eq_true (by omega),Bool.true_and,
    Nat.testBit_div_two]

theorem add_tail_bit (X Y j : Nat) (hX : X%2=0) :
    (X/2+Y/2).testBit j=(X+Y).testBit (j+1) := by
  rw [← Nat.testBit_div_two]
  congr 1
  omega

end ECDSAAdd.Entrant.InteriorCarry
namespace ECDSAAdd.Entrant.DI4Merge
open Arithmetic InteriorCarry KRegs
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

theorem reg_tail (xs : List Wire) (s : BasisState) : regValue xs.tail s=regValue xs s/2 := by
  cases xs with
  | nil => simp [regValue]
  | cons a xs =>
    rw [TopCarry.regValue_cons']
    have h : (s a).toNat<2 := by cases s a <;> decide
    simp only [List.tail_cons]
    omega

/-- Two adjacent interior carries from two specified subtraction output bits. -/
theorem sub_bits_eq (r : Bool × Option Wire) (v : Bool) (k : Nat)
    (x y cs : List Wire) (ci : Wire) (hn : (ci::(x++y++cs)).Nodup)
    (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hr : ∀q∈r.2,q∉y ∧ q∉cs)
    (hi : s.basis ci=false) (heven : regValue x s.basis%2=0)
    (hxy : regValue x s.basis≤regValue y s.basis)
    (hk : k+3<y.length)
    (hbit : (!(regValue y s.basis-regValue x s.basis).testBit (k+2))=label r s.basis)
    (hbit2 : (!(regValue y s.basis-regValue x s.basis).testBit (k+3))=v) :
    run (sub r v k x y cs ci) m s=run (LowZero.subLowNC x y cs ci) m s := by
  have yn : y.Nodup := knd hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have nr := notRegister_correct y yn s []
  let u := run (notRegister y) [] s
  have un (q : Wire) (hq : q∉y) : u.basis q=s.basis q := by simp [u,nr,hq]
  have uy (q : Wire) (hq : q∈y) : u.basis q= !s.basis q := by simp [u,nr,hq]
  have noty (q : Wire) (hq : q∈x ∨ q∈cs ∨ q=ci) : q∉y := by
    rcases hq with hx|hc|rfl
    · exact kdis hn (fun q => by simp only [List.count_cons,List.count_append]; omega) q hx
    · exact kdis hn (fun q => by simp only [List.count_cons,List.count_append]; omega) q hc
    · exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hvx : regValue x.tail u.basis=regValue x s.basis/2 := by
    rw [regValue_congr x.tail _ s.basis (fun q hq => un q (noty q (Or.inl (List.mem_of_mem_tail hq)))),reg_tail]
  have hvy : regValue y.tail u.basis=2^(y.length-1)-1-regValue y s.basis/2 := by
    rw [regValue_congr y.tail _ (fun q => !s.basis q) (fun q hq => uy q (List.mem_of_mem_tail hq)),
      regValue_complement,reg_tail,List.length_tail]
  have hvci : u.basis ci=false := (un ci (noty ci (Or.inr (Or.inr rfl)))).trans hi
  have hlabel : label r u.basis=label r s.basis := by
    unfold label
    congr 1
    cases he : r.2 with
    | none => rfl
    | some q => exact un q ((hr q (by rw [he]; simp)).1)
  apply sub_eq r v k x y cs ci (KnownTop.tail_nodup x y cs ci hn) s m
  · intro q hq
    rw [un q (noty q (Or.inr (Or.inl (List.mem_of_mem_tail hq))))]
    exact hclean q (List.mem_of_mem_tail hq)
  · intro q hq hmem
    exact (hr q hq).2 (List.mem_of_mem_tail hmem)
  · apply of_sum_testBit
    rw [hvx,hvy,hvci,Bool.toNat_false,Nat.add_zero,hlabel]
    exact (sub_tail_bit _ _ _ _ (by omega) (by omega) heven hxy (regValue_lt y s.basis)).trans hbit
  · apply of_sum_testBit
    rw [hvx,hvy,hvci,Bool.toNat_false,Nat.add_zero]
    simpa only [label,Prod.fst,Prod.snd,Option.elim_none,Bool.xor_false,Nat.add_assoc] using
      (sub_tail_bit _ _ _ _ (by omega) (by omega) heven hxy (regValue_lt y s.basis)).trans hbit2

end ECDSAAdd.Entrant.DI4Merge
namespace ECDSAAdd.Entrant.DI4Merge
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem square_mod4 (b : Nat) : (b*b)%4=b%2 := by
  have hh : b%4<4 := Nat.mod_lt _ (by decide)
  have he : (b*b)%4=((b%4)*(b%4))%4 := Nat.mul_mod _ _ _
  interval_cases hr : b%4 <;> norm_num at he <;> omega

theorem partial_bits (h a b : Nat) (_hh : 1≤h) (ha : a<2^h) :
    (((a+2^h*b)^2/2^h-2*a*b).testBit h=b.testBit 0) ∧
    (((a+2^h*b)^2/2^h-2*a*b).testBit (h+1)=false) := by
  let P := 2^h
  have hp : 0<P := Nat.two_pow_pos _
  have aq : a^2/P<P := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    dsimp only [P]
    nlinarith
  have ex : (a+P*b)^2=a^2+P*(P*b^2+2*a*b) := by ring
  have exd : (a+P*b)^2/P=a^2/P+(P*b^2+2*a*b) := by
    rw [ex,Nat.add_mul_div_left _ _ hp]
  have ed : ((a+P*b)^2/P-2*a*b)/P=b^2 := by
    rw [exd,show a^2/P+(P*b^2+2*a*b)-2*a*b=a^2/P+P*b^2 by rw [← Nat.add_assoc,Nat.add_sub_cancel],
      Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt aq,Nat.zero_add]
  constructor
  · rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq]
    change decide ((((a+P*b)^2/P-2*a*b)/P)%2=1)=decide (b/1%2=1)
    rw [ed,Nat.div_one]
    have hm := square_mod4 b
    have hdiv := Nat.mod_add_div (b*b) 4
    have sq2 : (b*b)%2=b%2 := by omega
    simp only [pow_two,sq2]
  · rw [Nat.testBit_eq_decide_div_mod_eq,show 2^(h+1)=P*2 by dsimp only [P]; rw [pow_succ],← Nat.div_div_eq_div_mul]
    change decide (((((a+P*b)^2/P-2*a*b)/P)/2)%2=1)=false
    rw [ed]
    have hm := square_mod4 b
    have hb : b%2<2 := Nat.mod_lt _ (by decide)
    have hdiv := Nat.mod_add_div (b*b) 4
    simp only [pow_two] at *
    have hz : (b*b)/2%2=0 := by omega
    simp [hz]
end ECDSAAdd.Entrant.DI4Merge
namespace ECDSAAdd.Entrant.DI4Merge
open Arithmetic InteriorCarry KRegs
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

def merge (R : KRegs) : Program :=
  sub (true,some (R.hi.headD 0)) true (R.h-2) (R.T++R.zM) R.dmid
    (R.carry.take (R.dmid.length-1)) R.cin

theorem merge_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0)
    (hi0 : s.basis R.cin=false) : run (merge R) m s=run R.c8g m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have hTl := w.T; have hSl := w.S; have hCl := w.carry; have hDl := w.dst
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have ha : a<2^R.h := by simpa only [a,L0] using regValue_lt R.lo s.basis
  have zm : regValue R.zM s.basis=0 := KRegs.xz hz0 (fun q h => List.mem_of_mem_take h)
  have hX : regValue (R.T++R.zM) s.basis=2*a*b := by rw [regValue_append,hT0,zm]; simp [a,b]
  have hY : regValue R.dmid s.basis=(a+2^R.h*b)^2/2^R.h := by
    rw [show regValue R.dmid s.basis=regValue R.dst s.basis/2^R.h from
      CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by omega) s.basis,hd0,R.bank_value w]
  have hge : regValue (R.T++R.zM) s.basis≤regValue R.dmid s.basis := by
    rw [hX,hY]
    have ex : (a+2^R.h*b)^2=a^2+2^R.h*(2^R.h*b^2+2*a*b) := by ring
    rw [ex,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),← Nat.add_assoc]
    exact Nat.le_add_left _ _
  have nn : (R.cin::((R.T++R.zM)++R.dmid++R.carry.take (R.dmid.length-1))).Nodup :=
    knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have hine : R.hi≠[] := by intro e; have := congrArg List.length e; simp only [List.length_nil] at this; omega
  have hmem : R.hi.headD 0∈R.hi := by
    cases he : R.hi with
    | nil => exact False.elim (hine he)
    | cons a xs => simp
  have hlabel : s.basis (R.hi.headD 0)=b.testBit 0 := by
    have hb := LowZero.head_bit R.hi [] s.basis hine
    simpa only [List.append_nil,Nat.testBit_eq_decide_div_mod_eq,pow_zero,Nat.div_one] using hb
  have bp := partial_bits R.h a b (by omega) ha
  have e1 : R.h-2+2=R.h := by omega
  have e2 : R.h-2+3=R.h+1 := by omega
  have le := R.m8g_lens w
  rw [KRegs.c8g,LowZero.subLowNCG_eq _ _ _ _ le.1 le.2.1 le.2.2]
  apply sub_bits_eq _ true (R.h-2) _ _ _ _ nn s m
  · intro q hq; exact (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq)
  · intro q hq
    simp only [Option.mem_some_iff] at hq
    subst q
    constructor
    · exact kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) _ hmem
    · exact kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) _ hmem
  · exact hi0
  · rw [hX,show 2*a*b=2*(a*b) by ring,Nat.mul_mod]
    simp
  · exact hge
  · rw [L4]; omega
  · rw [hX,hY,e1,bp.1]
    simp only [label,Prod.fst,Prod.snd,Option.elim_some,hlabel,Bool.true_xor]
  · rw [hX,hY,e2,bp.2]
    rfl
end ECDSAAdd.Entrant.DI4Merge
namespace ECDSAAdd.Entrant.DI4Merge
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
private instance dec_instr (i : Instr) : Decidable (RecordedQuantum.PhysicalInstr (.gate i)) := by
  cases i <;> simp only [RecordedQuantum.PhysicalInstr,ProperGate] <;> infer_instance
private instance dec_physical (P : Program) : Decidable (GatePhysical P) := by
  unfold GatePhysical
  infer_instance

def Active (R : KRegs) : Prop :=
  wires (merge R) ⊆ wires R.c8g ∪ R.bank.toFinset ∧
  GatePhysical (merge R) ∧
  toffoliCount (merge R)+2=toffoliCount R.c8g ∧
  measurementCount (merge R)=measurementCount R.c8g ∧
  Challenge.gateSlots (merge R)≤Challenge.gateSlots R.c8g
instance (R : KRegs) : Decidable (Active R) := inferInstanceAs (Decidable (_ ∧ _))

def safe (R : KRegs) : Program := if Active R then merge R else R.c8g

theorem safe_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0)
    (hi0 : s.basis R.cin=false) : run (safe R) m s=run R.c8g m s := by
  by_cases h : Active R
  · rw [safe,if_pos h]
    exact merge_eq R w hn s m hd0 hT0 hz0 hc0 hi0
  · rw [safe,if_neg h]

theorem safe_resources (R : KRegs) :
    wires (safe R)⊆wires R.c8g ∪ R.bank.toFinset ∧
    (GatePhysical R.c8g → GatePhysical (safe R)) ∧
    measurementCount (safe R)=measurementCount R.c8g ∧
    Challenge.gateSlots (safe R)≤Challenge.gateSlots R.c8g := by
  by_cases h : Active R
  · rw [safe,if_pos h]
    exact ⟨h.1,fun _ => h.2.1,h.2.2.2.1,h.2.2.2.2⟩
  · rw [safe,if_neg h]
    exact ⟨Finset.subset_union_left,id,rfl,le_refl _⟩

theorem safe_tc (R : KRegs) (h : Active R) : toffoliCount (safe R)+2=toffoliCount R.c8g := by
  rw [safe,if_pos h]
  exact h.2.2.1

theorem c8g_eq_c8z (R : KRegs) (w : R.W) : R.c8g=R.c8z := by
  have l := R.m8g_lens w
  rw [KRegs.c8g,KRegs.c8z,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
end ECDSAAdd.Entrant.DI4Merge

namespace ECDSAAdd.Entrant.DI4Merge
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace MW

theorem affine_wires (r : Bool × Option Wire) (a b c : Wire) :
    wires (InteriorCarry.affine r a b c)⊆(a::b::c::r.2.toList).toFinset := by
  rcases r with ⟨v,r⟩
  cases v <;> cases r <;> intro q hq <;>
    simp [InteriorCarry.affine,wires,Instr.wires] at hq ⊢ <;> tauto

theorem add_wires (r : Bool × Option Wire) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    wires (InteriorCarry.add r k x y cs ci)⊆(ci::(x++y++cs)).toFinset ∪ r.2.toList.toFinset := by
  induction k generalizing x y cs ci with
  | zero =>
    have old : wires (addInPlace x y cs ci)⊆(ci::(x++y++cs)).toFinset ∪ r.2.toList.toFinset := by
      rw [addInPlace_wires _ _ _ _ hx hc]; exact Finset.subset_union_left
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact old
    have ht := addInPlace_wires (a'::as) (b'::bs) cs c (by simp at hx ⊢; omega) (by simp at hc ⊢; omega)
    intro q hq
    have ha := @affine_wires r a' b' c q
    simp only [InteriorCarry.add,wires_append,ht,eraseCarry_wires] at hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,Finset.notMem_empty,or_false] at hq ha ⊢
    tauto
  | succ k ih =>
    have old : wires (addInPlace x y cs ci)⊆(ci::(x++y++cs)).toFinset ∪ r.2.toList.toFinset := by
      rw [addInPlace_wires _ _ _ _ hx hc]; exact Finset.subset_union_left
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact old
    have ht := ih (a'::as) (b'::bs) cs c (by simp at hx ⊢; omega) (by simp at hc ⊢; omega)
    intro q hq
    have hqt := @ht q
    simp only [InteriorCarry.add,wires_append,majority,eraseCarry_wires,wires,Instr.wires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,List.mem_cons,
      List.mem_append,List.not_mem_nil,Finset.notMem_empty,or_false] at hq hqt ⊢
    tauto

theorem pair_wires (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    wires (InteriorCarry.pair r v k x y cs ci)⊆(ci::(x++y++cs)).toFinset ∪ r.2.toList.toFinset := by
  induction k generalizing x y cs ci with
  | zero =>
    have old : wires (addInPlace x y cs ci)⊆(ci::(x++y++cs)).toFinset ∪ r.2.toList.toFinset := by
      rw [addInPlace_wires _ _ _ _ hx hc]; exact Finset.subset_union_left
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact old
    have ht := add_wires (v,none) 0 (a'::as) (b'::bs) cs c
      (by simp at hx ⊢; omega) (by simp at hc ⊢; omega)
    intro q hq
    have hqt := @ht q
    have ha := @affine_wires r a' b' c q
    simp only [InteriorCarry.pair,wires_append,eraseCarry_wires,wires,Instr.wires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,List.mem_cons,
      List.mem_append,Option.toList_none,List.not_mem_nil,Finset.notMem_empty,or_false] at hq hqt ha ⊢
    tauto
  | succ k ih =>
    have old : wires (addInPlace x y cs ci)⊆(ci::(x++y++cs)).toFinset ∪ r.2.toList.toFinset := by
      rw [addInPlace_wires _ _ _ _ hx hc]; exact Finset.subset_union_left
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact old
    have ht := ih (a'::as) (b'::bs) cs c (by simp at hx ⊢; omega) (by simp at hc ⊢; omega)
    intro q hq
    have hqt := @ht q
    simp only [InteriorCarry.pair,wires_append,majority,eraseCarry_wires,wires,Instr.wires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,List.mem_cons,
      List.mem_append,List.not_mem_nil,Finset.notMem_empty,or_false] at hq hqt ⊢
    tauto

theorem sub_wires_inputs (r : Bool × Option Wire) (v : Bool) (k : Nat)
    (x y cs : List Wire) (ci : Wire) (hx : x.length=y.length)
    (hc : cs.length+1=y.length) (h2 : 2≤y.length) :
    wires (InteriorCarry.sub r v k x y cs ci)⊆(ci::(x++y++cs)).toFinset ∪ r.2.toList.toFinset := by
  rcases x with _|⟨a,as⟩ <;> rcases y with _|⟨b,bs⟩ <;> rcases cs with _|⟨c,cs⟩ <;>
    simp only [List.length_cons,List.length_nil] at hx hc h2 <;> try omega
  have ht := pair_wires r v k as bs cs ci (by omega) (by omega)
  intro q hq
  have hqt := @ht q
  simp only [InteriorCarry.sub,InteriorCarry.lowNC,InteriorCarry.low0,List.tail_cons,List.headD_cons,
    wires_append,notRegister_wires,wires,Instr.wires,correctionWires,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,List.mem_cons,
    List.mem_append,List.not_mem_nil,Finset.notMem_empty,or_false] at hq hqt ⊢
  tauto

theorem lowNC_wires_eq (x y cs : List Wire) (ci : Wire) (hx : x.length=y.length)
    (hc : cs.length+1=y.length) (h2 : 2≤y.length) :
    wires (LowZero.addLowNC x y cs ci)=(ci::(x++y++cs)).toFinset := by
  rcases x with _|⟨a,as⟩ <;> rcases y with _|⟨b,bs⟩ <;> rcases cs with _|⟨c,cs⟩ <;>
    simp only [List.length_cons,List.length_nil] at hx hc h2 <;> try omega
  have ht := addInPlace_wires as bs cs ci (by omega) (by omega)
  ext q
  simp only [LowZero.addLowNC,List.tail_cons,List.headD_cons,wires_append,ht,
    wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,Finset.notMem_empty,or_false]
  tauto

theorem subLow_wires_eq (x y cs : List Wire) (ci : Wire) (hx : x.length=y.length)
    (hc : cs.length+1=y.length) (h2 : 2≤y.length) :
    wires (LowZero.subLowNC x y cs ci)=(ci::(x++y++cs)).toFinset := by
  rw [LowZero.subLowNC,wires_append,wires_append,lowNC_wires_eq _ _ _ _ hx hc h2,notRegister_wires]
  ext q
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto

end MW

/-- Compositional replacement for the expensive concrete Finset wire decisions. -/
theorem merge_wires (R : KRegs) (w : R.W) :
    wires (merge R)⊆wires R.c8g ∪ R.bank.toFinset := by
  have l := R.m8g_lens w
  rw [KRegs.c8g,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2,
    MW.subLow_wires_eq _ _ _ _ l.1 l.2.1 l.2.2]
  have hp := MW.sub_wires_inputs (true,some (R.hi.headD 0)) true (R.h-2)
    (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin l.1 l.2.1 l.2.2
  have hine : R.hi≠[] := by
    have h4 := w.h4; have hh := w.hh
    intro he; have hlen := congrArg List.length he
    simp only [KRegs.hi,List.length_drop,List.length_nil] at hlen
    omega
  have himem : R.hi.headD 0∈R.hi := by
    cases he : R.hi with
    | nil => exact False.elim (hine he)
    | cons a as => simp
  have head : R.hi.headD 0∈R.bank := List.mem_of_mem_drop himem
  intro q hq
  have H := hp hq
  simp only [Finset.mem_union,Option.toList_some,List.toFinset_cons,List.toFinset_nil,
    Finset.mem_insert,Finset.notMem_empty,or_false] at H
  rcases H with H|H
  · exact Finset.mem_union_left _ (by simpa only [List.toFinset_cons,Finset.mem_insert] using H)
  · subst q; exact Finset.mem_union_right _ (List.mem_toFinset.mpr head)

end ECDSAAdd.Entrant.DI4Merge

namespace ECDSAAdd.Entrant.DI4Merge
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace MA

theorem affine_slots (r : Bool × Option Wire) (a b c : Wire) :
    Challenge.gateSlots (InteriorCarry.affine r a b c)≤4 := by
  rcases r with ⟨v,r⟩
  cases v <;> cases r <;>
    simp [InteriorCarry.affine,Challenge.gateSlots_append,Challenge.gateSlots,Challenge.instructionSlots]

theorem majority_slots (a b ci c : Wire) : Challenge.gateSlots (majority a b ci c)=6 := rfl

theorem add_slots (r : Bool × Option Wire) (k : Nat) (x y cs : List Wire) (ci : Wire) :
    Challenge.gateSlots (InteriorCarry.add r k x y cs ci)≤Challenge.gateSlots (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact le_refl _
    have h := affine_slots r a' b' c
    simp only [InteriorCarry.add,addInPlace,Challenge.gateSlots_append,majority_slots]
    omega
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact le_refl _
    have h := ih (a'::as) (b'::bs) cs c
    simp only [InteriorCarry.add,addInPlace,Challenge.gateSlots_append]
    omega

theorem pair_slots (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire) :
    Challenge.gateSlots (InteriorCarry.pair r v k x y cs ci)≤Challenge.gateSlots (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact le_refl _
    have h := affine_slots r a' b' c
    have t := add_slots (v,none) 0 (a'::as) (b'::bs) cs c
    simp only [InteriorCarry.pair,addInPlace,Challenge.gateSlots_append,majority_slots]
    omega
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact le_refl _
    have h := ih (a'::as) (b'::bs) cs c
    simp only [InteriorCarry.pair,addInPlace,Challenge.gateSlots_append]
    omega

theorem sub_slots (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire) :
    Challenge.gateSlots (InteriorCarry.sub r v k x y cs ci)≤Challenge.gateSlots (LowZero.subLowNC x y cs ci) := by
  have h := pair_slots r v k x.tail y.tail cs.tail ci
  simp only [InteriorCarry.sub,InteriorCarry.lowNC,InteriorCarry.low0,
    LowZero.subLowNC,LowZero.addLowNC,LowZero.addLow0,Challenge.gateSlots_append]
  omega

theorem sub_physical (r : Bool × Option Wire) (v : Bool) (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (hr : ∀q∈r.2,q∉cs)
    (hp : GatePhysical (LowZero.subLowNC x y cs ci)) : GatePhysical (InteriorCarry.sub r v k x y cs ci) := by
  have nd := KnownTop.tail_nodup x y cs ci hn
  simp only [LowZero.subLowNC,LowZero.addLowNC,LowZero.addLow0,gatePhysical_append] at hp
  have h := InteriorCarry.pair_physical r v k x.tail y.tail cs.tail ci nd
    (fun q hq hm => hr q hq (List.mem_of_mem_tail hm)) hp.1.2.1.1
  simp only [InteriorCarry.sub,InteriorCarry.lowNC,InteriorCarry.low0,gatePhysical_append]
  exact ⟨⟨hp.1.1,⟨⟨h,hp.1.2.1.2⟩,hp.1.2.2⟩⟩,hp.2⟩

end MA

theorem merge_tc (R : KRegs) (w : R.W) : toffoliCount (merge R)+2=toffoliCount R.c8g := by
  have l := R.m8g_lens w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4
  have hh := w.hh
  have h := InteriorCarry.low_counts (true,some (R.hi.headD 0)) true (R.h-2)
    (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_tail]; omega)
    (by simp only [List.length_tail]; omega)
    (by simp only [List.length_tail]; omega)
  rw [KRegs.c8g,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact h.2.2

theorem merge_measurements (R : KRegs) (w : R.W) :
    measurementCount (merge R)=measurementCount R.c8g := by
  have l := R.m8g_lens w
  rw [KRegs.c8g,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact InteriorCarry.sub_mc _ _ _ _ _ _ _

theorem merge_slots (R : KRegs) (w : R.W) : Challenge.gateSlots (merge R)≤Challenge.gateSlots R.c8g := by
  have l := R.m8g_lens w
  rw [KRegs.c8g,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact MA.sub_slots _ _ _ _ _ _ _

theorem merge_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (merge R) := by
  have l := R.m8g_lens w
  have nn : (R.cin::((R.T++R.zM)++R.dmid++R.carry.take (R.dmid.length-1))).Nodup := by
    exact knd hn (fun q => by
      have c := R.counts q
      simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢
      omega)
  have hine : R.hi≠[] := by
    have h4 := w.h4; have hh := w.hh
    intro he; have hlen := congrArg List.length he
    simp only [KRegs.hi,List.length_drop,List.length_nil] at hlen
    omega
  have himem : R.hi.headD 0∈R.hi := by
    cases he : R.hi with
    | nil => exact False.elim (hine he)
    | cons a as => simp
  have hr : ∀q∈(true,some (R.hi.headD 0)).2,q∉R.carry.take (R.dmid.length-1) := by
    intro q hq
    simp only [Option.mem_some_iff] at hq
    subst q
    exact kdis hn (fun q => by
      have c := R.counts q
      simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢
      omega) _ himem
  have old := R.c8g_physical hn
  rw [KRegs.c8g,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2] at old
  exact MA.sub_physical _ _ _ _ _ _ _ nn hr old

theorem active_of_W (R : KRegs) (w : R.W) (hn : R.all.Nodup) : Active R :=
  ⟨merge_wires R w,merge_physical R w hn,merge_tc R w,merge_measurements R w,merge_slots R w⟩

end ECDSAAdd.Entrant.DI4Merge

namespace ECDSAAdd.Entrant.DI4Square
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem raw_top_aux (Q x : Nat) (hQ : 0 < Q) (hx : x < 2*Q) :
    (2*Q*Q ≤ x*x+x+(Q-1-x%Q)*(2*Q)) ↔ Q ≤ x := by
  have hv : x%Q < Q := Nat.mod_lt _ hQ
  have hd : x/Q ≤ 1 := by
    have := Nat.div_lt_of_lt_mul (show x < Q*2 by omega)
    omega
  have split := Nat.mod_add_div x Q
  obtain ⟨k,hk⟩ : ∃ k, Q = x%Q+1+k := ⟨Q-1-x%Q,by omega⟩
  have ek : Q-1-x%Q=k := by omega
  rw [ek]
  generalize x%Q=v at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hb|hb
  · rw [hb] at split
    have ex : x=v := by omega
    subst x
    constructor
    · intro h
      nlinarith [Nat.zero_le (v*k), Nat.zero_le (k*k)]
    · intro h; omega
  · rw [hb] at split
    have ex : x=v+Q := by omega
    rw [ex]
    constructor
    · omega
    · intro _
      nlinarith [Nat.zero_le (v*v),Nat.zero_le (v*k),Nat.zero_le (k*k)]

theorem raw_top (n x : Nat) (hn : 1≤n) (hx : x<2^n) :
    (2^(2*n-1) ≤ rawValue n x) ↔ 2^(n-1) ≤ x := by
  have hP : 2^n=2*2^(n-1) := KRegs.pow_two_mul_split n hn
  have hPP : 2^(2*n-1)=2*2^(n-1)*2^(n-1) := by
    have he : 2*n-1=(n-1)+(n-1)+1 := by omega
    rw [he,pow_succ,pow_add]
    ring
  unfold rawValue signedDiagValue
  rw [if_neg (by omega),hP,hPP]
  simpa only [pow_two, Nat.add_assoc] using raw_top_aux _ _ (Nat.two_pow_pos _) (by rwa [hP] at hx)

theorem top_true_iff (lo : List Wire) (q : Wire) (b : BasisState) :
    (2^lo.length ≤ regValue (lo++[q]) b) ↔ b q = true := by
  rw [regValue_append]
  have eq : regValue [q] b = (b q).toNat := by cases h : b q <;> simp [regValue,h]
  rw [eq]
  have h := regValue_lt lo b
  cases hb : b q <;> simp [hb] <;> omega

theorem raw_top_wire (lo dl : List Wire) (x y : Wire) (s : BasisState)
    (hl : dl.length = 2*(lo.length+1)-1)
    (hv : regValue (dl++[y]) s = rawValue (lo.length+1) (regValue (lo++[x]) s)) :
    s y = s x := by
  have ht := raw_top (lo.length+1) (regValue (lo++[x]) s) (by omega) (by
    simpa only [List.length_append,List.length_singleton] using regValue_lt (lo++[x]) s)
  have hy := top_true_iff dl y s
  have hx := top_true_iff lo x s
  rw [hv,hl] at hy
  simp only [Nat.add_sub_cancel] at ht
  have he : s y = true ↔ s x = true := hy.symm.trans (ht.trans hx)
  exact Bool.eq_iff_iff.mpr he
end ECDSAAdd.Entrant.DI4Square
namespace ECDSAAdd.Entrant.DI4Square
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem split_last (xs : List Wire) (hx : xs≠[]) :
    xs.take (xs.length-1) ++ [xs.getD (xs.length-1) 0] = xs := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b bs =>
      simpa only [List.length_cons,Nat.add_sub_cancel,List.take_succ_cons,List.getD_cons_succ,List.cons_append]
        using congrArg (List.cons a) (ih (by simp))

theorem raw_top_getD (xs dst : List Wire) (s : BasisState)
    (hx : 1≤xs.length) (hd : dst.length=2*xs.length)
    (hv : regValue dst s=rawValue xs.length (regValue xs s)) :
    s (dst.getD (2*xs.length-1) 0)=s (xs.getD (xs.length-1) 0) := by
  have xne : xs≠[] := by intro e; simp [e] at hx
  have dne : dst≠[] := by
    intro e
    have eh : dst.length=0 := by rw [e]; rfl
    omega
  have ex := split_last xs xne
  have ed := split_last dst dne
  have el : (xs.take (xs.length-1)).length+1=xs.length := by simp; omega
  have dl : (dst.take (dst.length-1)).length = 2*((xs.take (xs.length-1)).length+1)-1 := by simp only [List.length_take,Nat.min_eq_left (Nat.sub_le _ _)]; omega
  have rv : regValue (dst.take (dst.length-1)++[dst.getD (dst.length-1) 0]) s =
      rawValue ((xs.take (xs.length-1)).length+1)
        (regValue (xs.take (xs.length-1)++[xs.getD (xs.length-1) 0]) s) := by rw [ed,ex,el]; exact hv
  simpa only [hd] using raw_top_wire _ _ _ _ s dl rv
end ECDSAAdd.Entrant.DI4Square
namespace ECDSAAdd.Entrant.DI4Square
open ECDSAAdd Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Recover an adder's last carry from one unchanged source label and the top output bit. -/
theorem recover_top_majority (P B : Program) (bit : MappedBit) (y cin c top label : Wire)
    (hn : [y,cin,c].Nodup) (ha : ∀ q∈bit.wire, q∉[y,cin,c])
    (hct : top≠c)
    (hcP : ∀ s m, (run P m s).basis c=s.basis c)
    (htP : ∀ s m, (run P m s).basis top=s.basis top)
    (hlP : ∀ s m, (run P m s).basis label=s.basis label)
    (htB : top∉wires B) (hmcP : measurementCount P=0)
    (s : State) (m : List Bool) (hc0 : s.basis c=false)
    (hout : (run (P++mappedMajority bit y cin c++[.CX c top]++B) m s).basis top=s.basis label) :
    run (P++[.CX label c,.CX top c]++[.CX c top]++B) m s =
      run (P++mappedMajority bit y cin c++[.CX c top]++B) m s := by
  let t := run P [] s
  let K := carryBit (bit.value t.basis) (t.basis y) (t.basis cin)
  have htc : t.basis c=false := (hcP s []).trans hc0
  have htt : t.basis top=s.basis top := htP s []
  have htl : t.basis label=s.basis label := hlP s []
  have hm : measurementCount (mappedMajority bit y cin c)=0 := (mappedBit_counts bit y cin c).2.1
  have eM (r : List Bool) : run (mappedMajority bit y cin c) r t =
      (⟨t.phase,writeBit t.basis c K⟩ : State) := by
    rw [mappedMajority_correct _ _ _ _ hn ha]
    simp only [htc,Bool.false_xor]
    rfl
  have ev : (run (P++mappedMajority bit y cin c++[.CX c top]++B) m s).basis top = (t.basis top ^^ K) := by
    simp only [List.append_assoc]
    rw [run_append P, hmcP, List.take_zero,List.drop_zero]
    change (run (mappedMajority bit y cin c++([.CX c top]++B)) m t).basis top=_
    rw [run_append (mappedMajority bit y cin c),hm,List.take_zero,List.drop_zero,eM]
    rw [run_append [.CX c top] B,show measurementCount [.CX c top]=0 from rfl,List.take_zero,List.drop_zero]
    rw [run_preserves_outside _ _ _ _ htB]
    simp [run,writeBit,hct]
  have hK : K=(t.basis label ^^ t.basis top) := by
    rw [ev,← htl] at hout
    have flip (a b k : Bool) : (a ^^ k)=b → k=(b ^^ a) := by
      cases a <;> cases b <;> cases k <;> decide
    exact flip _ _ _ hout
  have eNew : run [.CX label c,.CX top c] [] t=run (mappedMajority bit y cin c) [] t := by
    rw [eM]
    apply congrArg (State.mk t.phase)
    funext q
    by_cases hq : q=c
    · subst q
      simp [run,writeBit,Function.update,htc,hct,hK]
    · simp [run,writeBit,Function.update,hq]
  simp only [List.append_assoc]
  rw [run_append P,hmcP,List.take_zero,List.drop_zero,
      run_append P,hmcP,List.take_zero,List.drop_zero]
  rw [run_append [.CX label c,.CX top c],run_append (mappedMajority bit y cin c),hm]
  simp only [show measurementCount [.CX label c,.CX top c]=0 from rfl,List.take_zero,List.drop_zero]
  rw [eNew]
end ECDSAAdd.Entrant.DI4Square
namespace ECDSAAdd.Entrant.DI4Square
open ECDSAAdd Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure MajFrame where
  bit : MappedBit
  y : Wire
  cin : Wire
  c : Wire

def MajFrame.program (a : MajFrame) : Program := mappedMajority a.bit a.y a.cin a.c

def MajFrame.Good (a : MajFrame) : Prop :=
  [a.y,a.cin,a.c].Nodup ∧ ∀q∈a.bit.wire,q∉[a.y,a.cin,a.c]
instance (a : MajFrame) : Decidable a.Good := inferInstanceAs (Decidable (_ ∧ _))

theorem MajFrame.keep (a : MajFrame) (ha : a.Good) (q : Wire) (hq : q≠a.c)
    (s : State) (m : List Bool) : (run a.program m s).basis q=s.basis q := by
  rw [MajFrame.program,mappedMajority_correct _ _ _ _ ha.1 ha.2]
  simp [writeBit,hq]

def majPrefix (xs : List MajFrame) : Program := xs.flatMap MajFrame.program

theorem majPrefix_keep (xs : List MajFrame) (q : Wire)
    (hg : ∀a∈xs,a.Good) (hq : ∀a∈xs,q≠a.c) (s : State) (m : List Bool) :
    (run (majPrefix xs) m s).basis q=s.basis q := by
  induction xs generalizing s m with
  | nil => rfl
  | cons a xs ih =>
    change (run (a.program ++ majPrefix xs) m s).basis q=s.basis q
    rw [run_append]
    rw [ih (by intros; apply hg; simp_all) (by intros; apply hq; simp_all)]
    exact a.keep (hg a (by simp)) q (hq a (by simp)) s _

theorem majPrefix_mc (xs : List MajFrame) : measurementCount (majPrefix xs)=0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [majPrefix,List.flatMap_cons,measurementCount_append,MajFrame.program,
      (mappedBit_counts a.bit a.y a.cin a.c).2.1]
    simpa only [majPrefix,Nat.zero_add] using ih

end ECDSAAdd.Entrant.DI4Square
namespace ECDSAAdd.Entrant.DI4Square
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def diagPre (xs dst carry : List Wire) (cin : Wire) : Program :=
  head1Pre (xs.getD 0 0) (dst.getD 0 0) cin (carry.getD 0 0) (xs.getD 1 0) (dst.getD 1 0) ++
  [.CX (dst.getD 2 0) (carry.getD 1 0),
   .CX (xs.getD 1 0) (carry.getD 1 0), .CX (xs.getD 1 0) (carry.getD 0 0),
   .CX (xs.getD 1 0) (dst.getD 1 0)]

def diagFrames (xs dst carry : List Wire) : List MajFrame :=
  (List.range' 2 (2*xs.length-4)).map (fun i =>
    ⟨(mappedDiagonal xs).getD i ⟨none,false⟩,dst.getD i 0,carry.getD (i-1) 0,carry.getD i 0⟩)

def diagP (xs dst carry : List Wire) (cin : Wire) : Program :=
  diagPre xs dst carry cin ++ majPrefix (diagFrames xs dst carry)

def diagB (xs dst carry : List Wire) (cin : Wire) : Program :=
  (dAddZ2 xs dst carry cin).drop (14*xs.length-8)

def diagTop (xs dst carry : List Wire) (cin : Wire) : Program :=
  diagP xs dst carry cin ++
  [.CX (xs.getD (xs.length-1) 0) (carry.getD (2*xs.length-2) 0),
   .CX (dst.getD (2*xs.length-1) 0) (carry.getD (2*xs.length-2) 0)] ++
  [.CX (carry.getD (2*xs.length-2) 0) (dst.getD (2*xs.length-1) 0)] ++
  diagB xs dst carry cin

def diagShape (xs dst carry : List Wire) (cin : Wire) : Prop :=
  let n := xs.length
  let c := carry.getD (2*n-2) 0
  let top := dst.getD (2*n-1) 0
  let label := xs.getD (n-1) 0
  let bit : MappedBit := ⟨some (xs.getD (n-2) 0),true⟩
  let y := dst.getD (2*n-2) 0
  let ci := carry.getD (2*n-3) 0
  dAddZ2 xs dst carry cin = diagP xs dst carry cin ++ mappedMajority bit y ci c ++ [.CX c top] ++ diagB xs dst carry cin ∧
  [y,ci,c].Nodup ∧ (∀q∈bit.wire,q∉[y,ci,c]) ∧ top≠c ∧
  c∉wires (diagPre xs dst carry cin) ∧ top∉wires (diagPre xs dst carry cin) ∧
  label∉wires (diagPre xs dst carry cin) ∧
  (∀a∈diagFrames xs dst carry,a.Good) ∧
  (∀a∈diagFrames xs dst carry,c≠a.c ∧ top≠a.c ∧ label≠a.c) ∧
  top∉wires (diagB xs dst carry cin) ∧
  wires (diagTop xs dst carry cin) ⊆ wires (dAddZ2 xs dst carry cin) ∧
  GatePhysical (diagTop xs dst carry cin) ∧
  toffoliCount (diagTop xs dst carry cin)+1=toffoliCount (dAddZ2 xs dst carry cin) ∧
  measurementCount (diagTop xs dst carry cin)=measurementCount (dAddZ2 xs dst carry cin) ∧
  Challenge.gateSlots (diagTop xs dst carry cin)≤Challenge.gateSlots (dAddZ2 xs dst carry cin)

private instance dec_instr (i : Instr) : Decidable (RecordedQuantum.PhysicalInstr (.gate i)) := by
 cases i <;> simp only [RecordedQuantum.PhysicalInstr,ProperGate] <;> infer_instance
private instance dec_physical (P : Program) : Decidable (GatePhysical P) := by
 unfold GatePhysical
 infer_instance

instance (xs dst carry : List Wire) (cin : Wire) : Decidable (diagShape xs dst carry cin) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem diagP_mc (xs dst carry : List Wire) (cin : Wire) : measurementCount (diagP xs dst carry cin)=0 := by
  simp [diagP,diagPre,head1Pre,majPrefix_mc,measurementCount]

theorem diagP_keep (xs dst carry : List Wire) (cin q : Wire)
    (hp : q∉wires (diagPre xs dst carry cin))
    (hg : ∀a∈diagFrames xs dst carry,a.Good)
    (hq : ∀a∈diagFrames xs dst carry,q≠a.c) (s : State) (m : List Bool) :
    (run (diagP xs dst carry cin) m s).basis q=s.basis q := by
  rw [diagP,run_append,majPrefix_keep _ _ hg hq]
  exact run_preserves_outside _ _ _ _ hp

theorem diagTop_eq (xs dst carry : List Wire) (cin : Wire) (h : diagShape xs dst carry cin)
    (s : State) (m : List Bool) (hc : s.basis (carry.getD (2*xs.length-2) 0)=false)
    (hout : (run (dAddZ2 xs dst carry cin) m s).basis (dst.getD (2*xs.length-1) 0)=s.basis (xs.getD (xs.length-1) 0)) :
    run (diagTop xs dst carry cin) m s=run (dAddZ2 xs dst carry cin) m s := by
  obtain ⟨he,hn,ha,hct,hcp,htp,hlp,hg,hqc,htB,_hres⟩ := h
  rw [he] at hout ⊢
  exact recover_top_majority _ _ _ _ _ _ _ _ hn ha hct
    (diagP_keep _ _ _ _ _ hcp hg (fun a ha => (hqc a ha).1))
    (diagP_keep _ _ _ _ _ htp hg (fun a ha => (hqc a ha).2.1))
    (diagP_keep _ _ _ _ _ hlp hg (fun a ha => (hqc a ha).2.2)) htB
    (diagP_mc _ _ _ _) s m hc hout

end ECDSAAdd.Entrant.DI4Square
namespace ECDSAAdd.Entrant.DI4Square
open ECDSAAdd Arithmetic DiagSq KRegs
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem transition_top (R : KRegs) (hn : R.all.Nodup) (base : State)
    (hc0 : regValue R.carry base.basis=0)
    (i : Fin 4) (xs dst : List Wire) (v w : Fin 4 → Int)
    (hx : 1≤xs.length) (hd : dst.length=2*xs.length)
    (hbank : ∀q∈xs,q∈R.bank) (hreg : reg R i=dst)
    (hval : w i=(rawValue xs.length (regValue xs base.basis) : Nat))
    (hshape : diagShape xs dst R.carry R.cin)
    (hcmem : R.carry.getD (2*xs.length-2) 0∈R.carry)
    (old : Transition R base v w (dAddZ2 xs dst R.carry R.cin)) :
    Transition R base v w (diagTop xs dst R.carry R.cin) := by
  intro t m ht
  have ho := old t m ht
  have keepBase (u : State) (z : Fin 4 → Int) (hu : Shape R base u z) (q : Wire)
      (hq : q∈R.bank ∨ q∈R.carry) : u.basis q=base.basis q := by
    have oo := R.outside hn q (hq.elim Or.inl (fun h => Or.inr (Or.inr (Or.inr (Or.inl h)))))
    exact hu.rest q oo.1 oo.2.1 oo.2.2
  have outSource : regValue xs (run (dAddZ2 xs dst R.carry R.cin) m t).basis=regValue xs base.basis :=
    regValue_congr _ _ _ (fun q hq => keepBase _ _ ho q (Or.inl (hbank q hq)))
  have hv : regValue dst (run (dAddZ2 xs dst R.carry R.cin) m t).basis=
      rawValue xs.length (regValue xs base.basis) := by
    have r := ho.exact i (rawValue xs.length (regValue xs base.basis)) hval (by
      rw [hreg,hd]
      exact rawValue_bound xs base.basis hx)
    simpa only [hreg] using r
  have hh := raw_top_getD xs dst (run (dAddZ2 xs dst R.carry R.cin) m t).basis hx hd (by
    rw [outSource]; exact hv)
  have labelmem : xs.getD (xs.length-1) 0∈xs := RawClearCarryIntegration.getD_mem xs _ (by omega)
  have hlabel : (run (dAddZ2 xs dst R.carry R.cin) m t).basis (xs.getD (xs.length-1) 0)=
      t.basis (xs.getD (xs.length-1) 0) :=
    (keepBase _ _ ho _ (Or.inl (hbank _ labelmem))).trans
      (keepBase _ _ ht _ (Or.inl (hbank _ labelmem))).symm
  rw [hlabel] at hh
  have hcarry : t.basis (R.carry.getD (2*xs.length-2) 0)=false :=
    (keepBase _ _ ht _ (Or.inr hcmem)).trans ((regValue_zero _ _).mp hc0 _ hcmem)
  rw [diagTop_eq _ _ _ _ hshape t m hcarry hh]
  exact ho
end ECDSAAdd.Entrant.DI4Square
namespace ECDSAAdd.Entrant.DI4Square
open ECDSAAdd Arithmetic DiagSq KRegs
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def diagSafe (xs dst carry : List Wire) (cin : Wire) : Program :=
  if diagShape xs dst carry cin then diagTop xs dst carry cin else dAddZ2 xs dst carry cin

theorem diagSafe_resources (xs dst carry : List Wire) (cin : Wire) :
    wires (diagSafe xs dst carry cin) ⊆ wires (dAddZ2 xs dst carry cin) ∧
    (GatePhysical (dAddZ2 xs dst carry cin) → GatePhysical (diagSafe xs dst carry cin)) ∧
    measurementCount (diagSafe xs dst carry cin)=measurementCount (dAddZ2 xs dst carry cin) ∧
    Challenge.gateSlots (diagSafe xs dst carry cin)≤Challenge.gateSlots (dAddZ2 xs dst carry cin) := by
  by_cases h : diagShape xs dst carry cin
  · rw [diagSafe,if_pos h]
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hw,hp,_,hm,hs⟩ := h
    exact ⟨hw,fun _ => hp,hm,hs⟩
  · rw [diagSafe,if_neg h]
    exact ⟨Finset.Subset.refl _,id,rfl,le_refl _⟩

theorem transition_safe (R : KRegs) (hn : R.all.Nodup) (base : State)
    (hc0 : regValue R.carry base.basis=0)
    (i : Fin 4) (xs dst : List Wire) (v w : Fin 4 → Int)
    (hx : 1≤xs.length) (hd : dst.length=2*xs.length)
    (hbank : ∀q∈xs,q∈R.bank) (hreg : reg R i=dst)
    (hval : w i=(rawValue xs.length (regValue xs base.basis) : Nat))
    (hcmem : R.carry.getD (2*xs.length-2) 0∈R.carry)
    (old : Transition R base v w (dAddZ2 xs dst R.carry R.cin)) :
    Transition R base v w (diagSafe xs dst R.carry R.cin) := by
  by_cases h : diagShape xs dst R.carry R.cin
  · rw [diagSafe,if_pos h]
    exact transition_top R hn base hc0 i xs dst v w hx hd hbank hreg hval h hcmem old
  · rwa [diagSafe,if_neg h]
end ECDSAAdd.Entrant.DI4Square
namespace ECDSAAdd.Entrant.DI4LastCarry
open ECDSAAdd Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Recover an adder's last carry from one unchanged source label and the top output bit. -/
theorem recover_last_majority (P B : Program) (bit : MappedBit) (y cin c top label x : Wire)
    (hn : [y,cin,c].Nodup) (ha : ∀ q∈bit.wire, q∉[y,cin,c])
    (hct : top≠c) (hxc : x≠c)
    (hcP : ∀ s m, (run P m s).basis c=s.basis c)
    (htP : ∀ s m, (run P m s).basis top=s.basis top)
    (hlP : ∀ s m, (run P m s).basis label=s.basis label)
    (hxP : ∀ s m, (run P m s).basis x=s.basis x)
    (htB : top∉wires B) (hmcP : measurementCount P=0)
    (s : State) (m : List Bool) (hc0 : s.basis c=false) (hx0 : s.basis x=false)
    (hout : (run (P++mappedMajority bit y cin c++[.CX x top,.CX c top]++B) m s).basis top=s.basis label) :
    run (P++[.CX label c,.CX top c]++[.CX x top,.CX c top]++B) m s =
      run (P++mappedMajority bit y cin c++[.CX x top,.CX c top]++B) m s := by
  let t := run P [] s
  let K := carryBit (bit.value t.basis) (t.basis y) (t.basis cin)
  have htc : t.basis c=false := (hcP s []).trans hc0
  have htt : t.basis top=s.basis top := htP s []
  have htl : t.basis label=s.basis label := hlP s []
  have htx : t.basis x=false := (hxP s []).trans hx0
  have hm : measurementCount (mappedMajority bit y cin c)=0 := (mappedBit_counts bit y cin c).2.1
  have eM (r : List Bool) : run (mappedMajority bit y cin c) r t =
      (⟨t.phase,writeBit t.basis c K⟩ : State) := by
    rw [mappedMajority_correct _ _ _ _ hn ha]
    simp only [htc,Bool.false_xor]
    rfl
  have ev : (run (P++mappedMajority bit y cin c++[.CX x top,.CX c top]++B) m s).basis top = (t.basis top ^^ K) := by
    simp only [List.append_assoc]
    rw [run_append P, hmcP, List.take_zero,List.drop_zero]
    change (run (mappedMajority bit y cin c++([.CX x top,.CX c top]++B)) m t).basis top=_
    rw [run_append (mappedMajority bit y cin c),hm,List.take_zero,List.drop_zero,eM]
    rw [run_append [.CX x top,.CX c top] B,show measurementCount [.CX x top,.CX c top]=0 from rfl,List.take_zero,List.drop_zero]
    rw [run_preserves_outside _ _ _ _ htB]
    simp [run,writeBit,hct,Ne.symm hct,hxc,htx]
  have hK : K=(t.basis label ^^ t.basis top) := by
    rw [ev,← htl] at hout
    have flip (a b k : Bool) : (a ^^ k)=b → k=(b ^^ a) := by
      cases a <;> cases b <;> cases k <;> decide
    exact flip _ _ _ hout
  have eNew : run [.CX label c,.CX top c] [] t=run (mappedMajority bit y cin c) [] t := by
    rw [eM]
    apply congrArg (State.mk t.phase)
    funext q
    by_cases hq : q=c
    · subst q
      simp [run,writeBit,Function.update,htc,hct,hK]
    · simp [run,writeBit,Function.update,hq]
  simp only [List.append_assoc]
  rw [run_append P,hmcP,List.take_zero,List.drop_zero,
      run_append P,hmcP,List.take_zero,List.drop_zero]
  rw [run_append [.CX label c,.CX top c],run_append (mappedMajority bit y cin c),hm]
  simp only [show measurementCount [.CX label c,.CX top c]=0 from rfl,List.take_zero,List.drop_zero]
  rw [eNew]

/-- Subtracting within the low word cannot change the top threshold. -/
theorem sub_low_top_iff (Z A q : Nat) (hq : 0<q) (ha : A≤Z%q) :
    (q≤Z-A) ↔ q≤Z := by
  constructor
  · intro h; exact h.trans (Nat.sub_le Z A)
  · intro h
    have hp : 0<Z/q := Nat.div_pos h hq
    have hm := Nat.mul_le_mul_left q (show 1≤Z/q by omega)
    simp only [Nat.mul_one] at hm
    have hd := Nat.mod_add_div Z q
    have he : Z-A=(Z%q-A)+q*(Z/q) := by omega
    rw [he]
    omega

end ECDSAAdd.Entrant.DI4LastCarry
namespace ECDSAAdd.Entrant.DI4LastCarry
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem split_last (xs : List Wire) (hx : xs≠[]) :
    xs.take (xs.length-1) ++ [xs.getD (xs.length-1) 0] = xs := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b bs =>
      simpa only [List.length_cons,Nat.add_sub_cancel,List.take_succ_cons,List.getD_cons_succ,List.cons_append]
        using congrArg (List.cons a) (ih (by simp))

theorem top_getD_iff (xs : List Wire) (s : BasisState) (hx : 1≤xs.length) :
    (2^(xs.length-1)≤regValue xs s) ↔ s (xs.getD (xs.length-1) 0)=true := by
  have h := DI4Square.top_true_iff (xs.take (xs.length-1)) (xs.getD (xs.length-1) 0) s
  rw [split_last xs (by intro e; simp [e] at hx)] at h
  simpa only [List.length_take,Nat.min_eq_left (Nat.sub_le _ _)] using h

/-- The existing trimmed-low subtract bound preserves the raw sum's high bit. -/
theorem raw_sub_top_getD (xs dst : List Wire) (s : BasisState) (A : Nat)
    (hx : 1≤xs.length) (hd : dst.length=2*xs.length)
    (hv : regValue dst s = rawValue xs.length (regValue xs s)-A)
    (ha : A≤rawValue xs.length (regValue xs s)%2^(dst.length-1)) :
    s (dst.getD (dst.length-1) 0)=s (xs.getD (xs.length-1) 0) := by
  have ht := top_getD_iff dst s (by omega)
  have hs := top_getD_iff xs s hx
  have hr := DI4Square.raw_top xs.length (regValue xs s) hx (regValue_lt xs s)
  have hb := sub_low_top_iff (rawValue xs.length (regValue xs s)) A
    (2^(dst.length-1)) (Nat.two_pow_pos _) ha
  have hh : (2^(dst.length-1)≤regValue dst s) ↔
      2^(xs.length-1)≤regValue xs s := by
    rw [hv]
    exact hb.trans (by simpa only [hd] using hr)
  exact Bool.eq_iff_iff.mpr (ht.symm.trans (hh.trans hs))

end ECDSAAdd.Entrant.DI4LastCarry
namespace ECDSAAdd.Entrant.DI4LastCarry
open ECDSAAdd Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure MajFrame where
  bit : MappedBit
  y : Wire
  cin : Wire
  c : Wire

def MajFrame.program (a : MajFrame) : Program := mappedMajority a.bit a.y a.cin a.c

def MajFrame.Good (a : MajFrame) : Prop :=
  [a.y,a.cin,a.c].Nodup ∧ ∀q∈a.bit.wire,q∉[a.y,a.cin,a.c]
instance (a : MajFrame) : Decidable a.Good := inferInstanceAs (Decidable (_ ∧ _))

theorem MajFrame.keep (a : MajFrame) (ha : a.Good) (q : Wire) (hq : q≠a.c)
    (s : State) (m : List Bool) : (run a.program m s).basis q=s.basis q := by
  rw [MajFrame.program,mappedMajority_correct _ _ _ _ ha.1 ha.2]
  simp [writeBit,hq]

def majPrefix (xs : List MajFrame) : Program := xs.flatMap MajFrame.program

theorem majPrefix_keep (xs : List MajFrame) (q : Wire)
    (hg : ∀a∈xs,a.Good) (hq : ∀a∈xs,q≠a.c) (s : State) (m : List Bool) :
    (run (majPrefix xs) m s).basis q=s.basis q := by
  induction xs generalizing s m with
  | nil => rfl
  | cons a xs ih =>
    change (run (a.program ++ majPrefix xs) m s).basis q=s.basis q
    rw [run_append]
    rw [ih (by intros; apply hg; simp_all) (by intros; apply hq; simp_all)]
    exact a.keep (hg a (by simp)) q (hq a (by simp)) s _

theorem majPrefix_mc (xs : List MajFrame) : measurementCount (majPrefix xs)=0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [majPrefix,List.flatMap_cons,measurementCount_append,MajFrame.program,
      (mappedBit_counts a.bit a.y a.cin a.c).2.1]
    simpa only [majPrefix,Nat.zero_add] using ih

end ECDSAAdd.Entrant.DI4LastCarry
namespace ECDSAAdd.Entrant.DI4LastCarry
open ECDSAAdd Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def frames (xs ys cs : List Wire) (ci : Wire) : List MajFrame :=
  (List.range' 1 (ys.length-3)).map fun i =>
    ⟨⟨some (xs.getD i 0),false⟩,ys.getD i 0,
      if i=1 then ci else cs.getD (i-1) 0,cs.getD i 0⟩
def pre (xs ys cs : List Wire) (ci : Wire) : Program := majPrefix (frames xs ys cs ci)
def old (xs ys cs : List Wire) (ci : Wire) : Program := LowZero.addLowNCG xs ys cs ci
def tail (xs ys cs : List Wire) (ci : Wire) : Program :=
  (old xs ys cs ci).drop (6*(ys.length-2)+2)
def program (xs ys cs : List Wire) (ci label : Wire) : Program :=
  let c := cs.getD (ys.length-2) 0
  let top := ys.getD (ys.length-1) 0
  let x := xs.getD (ys.length-1) 0
  pre xs ys cs ci ++ [.CX label c,.CX top c] ++ [.CX x top,.CX c top] ++ tail xs ys cs ci

def Shape (xs ys cs : List Wire) (ci label : Wire) : Prop :=
  let n := ys.length
  let c := cs.getD (n-2) 0
  let top := ys.getD (n-1) 0
  let x := xs.getD (n-1) 0
  let bit : MappedBit := ⟨some (xs.getD (n-2) 0),false⟩
  let y := ys.getD (n-2) 0
  let cin := cs.getD (n-3) 0
  old xs ys cs ci = pre xs ys cs ci ++ mappedMajority bit y cin c ++
    [.CX x top,.CX c top] ++ tail xs ys cs ci ∧
  [y,cin,c].Nodup ∧ (∀q∈bit.wire,q∉[y,cin,c]) ∧ top≠c ∧ x≠c ∧
  (∀a∈frames xs ys cs ci,a.Good) ∧
  (∀a∈frames xs ys cs ci,c≠a.c ∧ top≠a.c ∧ label≠a.c ∧ x≠a.c) ∧
  top∉wires (tail xs ys cs ci) ∧
  wires (program xs ys cs ci label) ⊆ insert label (wires (old xs ys cs ci)) ∧
  GatePhysical (program xs ys cs ci label) ∧
  toffoliCount (program xs ys cs ci label)+1=toffoliCount (old xs ys cs ci) ∧
  measurementCount (program xs ys cs ci label)=measurementCount (old xs ys cs ci) ∧
  Challenge.gateSlots (program xs ys cs ci label)≤Challenge.gateSlots (old xs ys cs ci)

private instance dec_instr (i : Instr) : Decidable (RecordedQuantum.PhysicalInstr (.gate i)) := by
  cases i <;> simp only [RecordedQuantum.PhysicalInstr,ProperGate] <;> infer_instance
private instance dec_physical (P : Program) : Decidable (GatePhysical P) := by
  unfold GatePhysical
  infer_instance
instance (xs ys cs : List Wire) (ci label : Wire) : Decidable (Shape xs ys cs ci label) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem pre_mc (xs ys cs : List Wire) (ci : Wire) : measurementCount (pre xs ys cs ci)=0 :=
  majPrefix_mc _
theorem pre_keep (xs ys cs : List Wire) (ci q : Wire)
    (hg : ∀a∈frames xs ys cs ci,a.Good)
    (hq : ∀a∈frames xs ys cs ci,q≠a.c) (s : State) (m : List Bool) :
    (run (pre xs ys cs ci) m s).basis q=s.basis q := majPrefix_keep _ _ hg hq s m

theorem program_eq (xs ys cs : List Wire) (ci label : Wire) (h : Shape xs ys cs ci label)
    (s : State) (m : List Bool)
    (hc : s.basis (cs.getD (ys.length-2) 0)=false)
    (hx : s.basis (xs.getD (ys.length-1) 0)=false)
    (hout : (run (old xs ys cs ci) m s).basis (ys.getD (ys.length-1) 0)=s.basis label) :
    run (program xs ys cs ci label) m s=run (old xs ys cs ci) m s := by
  obtain ⟨he,hn,ha,hct,hxc,hg,hq,htB,_⟩ := h
  rw [he] at hout
  unfold program
  rw [he]
  exact recover_last_majority _ _ _ _ _ _ _ _ _ hn ha hct hxc
    (pre_keep _ _ _ _ _ hg (fun a ha => (hq a ha).1))
    (pre_keep _ _ _ _ _ hg (fun a ha => (hq a ha).2.1))
    (pre_keep _ _ _ _ _ hg (fun a ha => (hq a ha).2.2.1))
    (pre_keep _ _ _ _ _ hg (fun a ha => (hq a ha).2.2.2)) htB
    (pre_mc _ _ _ _) s m hc hx hout

def safe (xs ys cs : List Wire) (ci label : Wire) : Program :=
  if Shape xs ys cs ci label then program xs ys cs ci label else old xs ys cs ci

theorem safe_eq (xs ys cs : List Wire) (ci label : Wire) (s : State) (m : List Bool)
    (hc : s.basis (cs.getD (ys.length-2) 0)=false)
    (hx : s.basis (xs.getD (ys.length-1) 0)=false)
    (hout : (run (old xs ys cs ci) m s).basis (ys.getD (ys.length-1) 0)=s.basis label) :
    run (safe xs ys cs ci label) m s=run (old xs ys cs ci) m s := by
  by_cases h : Shape xs ys cs ci label
  · rw [safe,if_pos h]; exact program_eq _ _ _ _ _ h s m hc hx hout
  · rw [safe,if_neg h]

theorem safe_resources (xs ys cs : List Wire) (ci label : Wire) :
    wires (safe xs ys cs ci label) ⊆ insert label (wires (old xs ys cs ci)) ∧
    (GatePhysical (old xs ys cs ci) → GatePhysical (safe xs ys cs ci label)) ∧
    measurementCount (safe xs ys cs ci label)=measurementCount (old xs ys cs ci) ∧
    Challenge.gateSlots (safe xs ys cs ci label)≤Challenge.gateSlots (old xs ys cs ci) := by
  by_cases h : Shape xs ys cs ci label
  · have hc := h
    obtain ⟨_,_,_,_,_,_,_,_,hw,hp,_,hm,hs⟩ := h
    rw [safe,if_pos hc]
    exact ⟨hw,fun _ => hp,hm,hs⟩
  · rw [safe,if_neg h]
    exact ⟨Finset.subset_insert _ _,id,rfl,le_refl _⟩

theorem safe_tc (xs ys cs : List Wire) (ci label : Wire) (h : Shape xs ys cs ci label) :
    toffoliCount (safe xs ys cs ci label)+1=toffoliCount (old xs ys cs ci) := by
  have hcopy := h
  obtain ⟨_,_,_,_,_,_,_,_,_,_,ht,_,_⟩ := h
  rw [safe,if_pos hcopy]
  exact ht


end ECDSAAdd.Entrant.DI4LastCarry
namespace ECDSAAdd.Entrant.DI4LastCarry
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def forR (R : KRegs) : Program :=
  safe (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (R.S.getD (R.S.length-1) 0)
def Active (R : KRegs) : Prop :=
  Shape (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (R.S.getD (R.S.length-1) 0)
instance (R : KRegs) : Decidable (Active R) := inferInstanceAs (Decidable (Shape _ _ _ _ _))

theorem forR_resources (R : KRegs) :
    wires (forR R) ⊆ insert (R.S.getD (R.S.length-1) 0) (wires R.c7g) ∧
    (GatePhysical R.c7g → GatePhysical (forR R)) ∧
    measurementCount (forR R)=measurementCount R.c7g ∧
    Challenge.gateSlots (forR R)≤Challenge.gateSlots R.c7g :=
  safe_resources _ _ _ _ _
theorem forR_tc (R : KRegs) (h : Active R) :
    toffoliCount (forR R)+1=toffoliCount R.c7g := safe_tc _ _ _ _ _ h

/-- Transport the existing c7 transition using its exact raw-sum-minus-low boundary. -/
theorem transition (R : KRegs) (hn : R.all.Nodup) (base : State)
    (hc0 : regValue R.carry base.basis=0) (hz0 : regValue R.z base.basis=0)
    (v ww : Fin 4 → Int) (A S Z : Nat)
    (hs : 1≤R.S.length) (hd : R.T.length=2*R.S.length)
    (hSlt : S<2^R.S.length) (hZlt : Z<2^R.T.length)
    (hraw : Z=rawValue R.S.length S) (ha : A≤Z%2^(R.T.length-1))
    (hSin : v 2=(S:Nat)) (hSout : ww 2=(S:Nat))
    (hTout : ww 3=((Z-A:Nat):Int))
    (hcMem : (R.carry.take (R.T.length-1)).getD (R.T.length-2) 0∈R.carry)
    (hxMem : (R.dhi++R.zB).getD (R.T.length-1) 0∈R.z)
    (ref : DiagSq.Transition R base v ww R.c7g) :
    DiagSq.Transition R base v ww (forR R) := by
  intro t m ht
  have ho := ref t m ht
  have beforeS : regValue R.S t.basis=S := ht.exact 2 S hSin hSlt
  have afterS : regValue R.S (run R.c7g m t).basis=S := ho.exact 2 S hSout hSlt
  have afterT : regValue R.T (run R.c7g m t).basis=Z-A :=
    ho.exact 3 (Z-A) hTout (lt_of_le_of_lt (Nat.sub_le Z A) hZlt)
  have outbit := raw_sub_top_getD R.S R.T (run R.c7g m t).basis A hs hd
    (by rw [afterS,afterT,←hraw]) (by rw [afterS,←hraw];exact ha)
  have oldbit := top_getD_iff R.S t.basis hs
  have newbit := top_getD_iff R.S (run R.c7g m t).basis hs
  rw [beforeS] at oldbit
  rw [afterS] at newbit
  have keepLabel : (run R.c7g m t).basis (R.S.getD (R.S.length-1) 0)=
      t.basis (R.S.getD (R.S.length-1) 0) :=
    Bool.eq_iff_iff.mpr (newbit.symm.trans oldbit)
  rw [keepLabel] at outbit
  have oc := R.outside hn _ (Or.inr (Or.inr (Or.inr (Or.inl hcMem))))
  have ox := R.outside hn _ (Or.inr (Or.inl hxMem))
  have cleanCarry := (ht.rest _ oc.1 oc.2.1 oc.2.2).trans
    ((regValue_zero _ _).mp hc0 _ hcMem)
  have cleanPad := (ht.rest _ ox.1 ox.2.1 ox.2.2).trans
    ((regValue_zero _ _).mp hz0 _ hxMem)
  have eqRun : run (forR R) m t=run R.c7g m t :=
    safe_eq _ _ _ _ _ t m cleanCarry cleanPad outbit
  rw [eqRun]
  exact ho

end ECDSAAdd.Entrant.DI4LastCarry
namespace ECDSAAdd.Entrant.DI4LastCarry
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem members (R : KRegs) (w : R.W) :
    (R.carry.take (R.T.length-1)).getD (R.T.length-2) 0∈R.carry ∧
    (R.dhi++R.zB).getD (R.T.length-1) 0∈R.z := by
  have h4 := w.h4
  have hh := w.hh
  have hS := w.S
  have hT := w.T
  have hz := w.z
  have hc := w.carry
  have hdhi := (R.lens w).2.2.2.1
  have ht2 : 2≤R.T.length := by omega
  have hcl : (R.carry.take (R.T.length-1)).length=R.T.length-1 := by
    simp only [List.length_take]
    omega
  refine ⟨?_,?_⟩
  · exact List.mem_of_mem_take (RawClearCarryIntegration.getD_mem _ _ (by rw [hcl];omega))
  · have hx : (R.dhi++R.zB).getD (R.T.length-1) 0=R.z.getD 1 0 := by
      have hi : R.T.length-1-R.dhi.length=1 := by omega
      unfold List.getD
      rw [List.getElem?_append_right (by omega),hi]
      simp only [KRegs.zB,List.getElem?_take_of_lt (show 1<2 by decide)]
    rw [hx]
    exact RawClearCarryIntegration.getD_mem _ _ (by omega)

theorem transition_w (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hc0 : regValue R.carry base.basis=0) (hz0 : regValue R.z base.basis=0)
    (v ww : Fin 4 → Int) (A S Z : Nat)
    (hSlt : S<2^R.S.length) (hZlt : Z<2^R.T.length)
    (hraw : Z=rawValue R.S.length S) (ha : A≤Z%2^(R.T.length-1))
    (hSin : v 2=(S:Nat)) (hSout : ww 2=(S:Nat))
    (hTout : ww 3=((Z-A:Nat):Int))
    (ref : DiagSq.Transition R base v ww R.c7g) :
    DiagSq.Transition R base v ww (forR R) := by
  have hs : 1≤R.S.length := by have := w.S;have := w.hh;have := w.h4;omega
  exact transition R hn base hc0 hz0 v ww A S Z hs w.T hSlt hZlt hraw ha
    hSin hSout hTout (members R w).1 (members R w).2 ref

end ECDSAAdd.Entrant.DI4LastCarry
namespace ECDSAAdd.Entrant.DI4Square
open ECDSAAdd Arithmetic DiagSq KRegs RawClearSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def clearWith (R : KRegs) (front : Program) : Program := front++(diagSafe R.lo R.dlo R.carry R.cin++
  diagSafe R.hi R.dhi R.carry R.cin++corrBackZ R++DI4LastCarry.forR R++RawClearCarryIntegration.c6 R++
  rawClearT R.S R.T R.pad R.carry++R.scl1591++rawClearT R.hi R.dhi R.pad R.carry++
  rawClearT R.lo R.dlo R.pad R.carry)


def clear (R : KRegs) : Program := clearWith R (DI4Merge.safe R)

def clearC (R : KRegs) : Program := R.smkT++clear R

theorem clearWith_correct (R : KRegs) (front : Program) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false)
    (hf : ∀r, run front r s=run R.c8g r s) :
    (run (clearWith R front) m s).phase=s.phase ∧
    regValue R.dst (run (clearWith R front) m s).basis=0 ∧
    regValue R.S (run (clearWith R front) m s).basis=0 ∧
    regValue R.T (run (clearWith R front) m s).basis=0 ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (clearWith R front) m s).basis q=s.basis q := by
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
  have st1New := transition_safe R hn s hc0 0 R.lo R.dlo _ _ (by omega) (by omega)
    (fun q h => List.mem_of_mem_take h) rfl (by simp only [vec, L0]; rfl)
    (RawClearCarryIntegration.getD_mem _ _ (by have := w.carry; omega)) st1'
  have st2New := transition_safe R hn s hc0 1 R.hi R.dhi _ _ (by omega)
    (by rw [L3,hhi]; omega) (fun q h => List.mem_of_mem_drop h) rfl
    (by simp only [vec,hhi]; rfl)
    (RawClearCarryIntegration.getD_mem _ _ (by have := w.carry; omega)) st2'
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
  have st5 := RawClearCarryIntegration.addlo_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d+B) Z hA (rawValue_even _ _ (by omega)) norm' hZ1 hb1 hA1 slt (RawClearCarryProbe.raw_even (R.h+1) S (by omega)) (RawClearCarryProbe.raw_mod8 (R.h+1) S (by omega))
  rw [norm'] at st5
  have hAZ : A≤Z := hb1.trans (Nat.mod_le _ _)
  have hTout : ((2*a*b : Nat) : Int)+d+B=((Z-A : Nat) : Int) := by
    rw [Nat.cast_sub hAZ]
    linarith only [norm']
  have st4New := DI4LastCarry.transition_w R w hn s hc0 hz0 _ _ A S Z slt hZ1
    (by rw [hSS]) hb1 rfl rfl hTout st4
  have st6 := rawclearSum_transitionT R w hn s hp0 hc0 A B S slt
  rw [hSS] at st6
  have st7 := Z5Diagonal.clearSum_transition R w he hn s hz0 hc0 hi0 A B 0
  have st8 := rawclearhi_transitionT R w he hn s hp0 hc0 A 0 0
  have st9 := rawclearlo_transitionT R w he hn s hp0 hc0 0 0 0
  have st3' : Transition R s (vec A B S (2*a*b : Nat))
      (vec A B S ((2*a*b : Nat)+d)) (corrBackZ R) := by
    (convert st3 using 1; try rfl)
    simp only [d]
    congr 1
    ring
  have tail := ((((((((st1New.seq st2New).seq st3').seq st4New).seq st5).seq st6).seq st7).seq st8).seq st9)
  have initial := clearZ_start_shape R w he hn s (m.take (measurementCount front)) hd0 hS0 hT0 hz0 hc0 hi0
  rw [← hf _] at initial
  have result := tail _ (m.drop (measurementCount front)) initial
  have final : Shape R s (run (clearWith R front) m s) (vec 0 0 0 0) := by
    simpa only [clearWith,run_append] using result
  refine ⟨final.phase,?_,final.exact 2 0 rfl (by norm_num),final.exact 3 0 rfl (by norm_num),final.rest⟩
  have zlo : regValue R.dlo (run (clearWith R front) m s).basis=0 := final.exact 0 0 rfl (by norm_num)
  have zhi : regValue R.dhi (run (clearWith R front) m s).basis=0 := final.exact 1 0 rfl (by norm_num)
  rw [R.dst_value w,zlo,zhi]
  simp


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
  exact clearWith_correct R (DI4Merge.safe R) w he hh hn s m hd0 hS0 hT0 hz0 hp0 hc0 hi0
    (fun r => DI4Merge.safe_eq R w hn s r hd0 hT0 hz0 hc0 hi0)

end ECDSAAdd.Entrant.DI4Square

namespace ECDSAAdd.Entrant.DI4Square
open Arithmetic DiagSq KRegs
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
variable (R : KRegs)
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
    rw [clearC,run_append,(R.smkT_counts w).2,
      R.smkT_run w hn s _ (by rw [hI.2,R.lo_mod w,R.hi_div w]) hI.1 hi0,←hu]
  rw [eq]
  refine ⟨c.1.trans r.1,c.2.1,?_,?_⟩
  · rw [regValue_append,c.2.2.1,c.2.2.2.1]; simp
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2.2.2 q h xS xT).trans (r.2.2 q xS)


end ECDSAAdd.Entrant.DI4Square

namespace ECDSAAdd.Entrant.DI4Square
open Arithmetic DiagSq KRegs
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.measurementCount ECDSAAdd.toffoliCount Challenge.gateSlots GatePhysical DI4Merge.safe diagSafe

theorem clearWith_resources (R : KRegs) (front : Program)
    (c : wires front⊆wires R.c8g ∪ R.bank.toFinset ∧
      (GatePhysical R.c8g → GatePhysical front) ∧
      measurementCount front=measurementCount R.c8g ∧
      Challenge.gateSlots front≤Challenge.gateSlots R.c8g) :
    wires (clearWith R front)⊆(wires (RawClearSquare.clear R) ∪ R.bank.toFinset) ∪ {R.S.getD (R.S.length-1) 0} ∧
    (GatePhysical (RawClearSquare.clear R) → GatePhysical (clearWith R front)) ∧
    measurementCount (clearWith R front)=measurementCount (RawClearSquare.clear R) ∧
    Challenge.gateSlots (clearWith R front)≤Challenge.gateSlots (RawClearSquare.clear R) := by
  have l := diagSafe_resources R.lo R.dlo R.carry R.cin
  have h := diagSafe_resources R.hi R.dhi R.carry R.cin
  have c7 := DI4LastCarry.forR_resources R
  refine ⟨?_,?_,?_,?_⟩
  · intro q hq
    have hl := @l.1 q
    have hh := @h.1 q
    have hc := @c.1 q
    have hc7 := @c7.1 q
    simp only [clearWith,RawClearSquare.clear,wires_append,Finset.mem_union,Finset.mem_singleton] at hq ⊢
    simp only [Finset.mem_union,Finset.mem_insert] at hc hc7
    clear l h c c7
    tauto
  · have lp := l.2.1; have hp := h.2.1; have cp := c.2.1; have c7p := c7.2.1
    simp only [clearWith,RawClearSquare.clear,gatePhysical_append]
    intro old
    clear l h c c7
    tauto
  · simp only [clearWith,RawClearSquare.clear,measurementCount_append,l.2.2.1,h.2.2.1,c.2.2.1,c7.2.2.1]
  · have ls := l.2.2.2; have hs := h.2.2.2; have cs := c.2.2.2; have c7s := c7.2.2.2
    simp only [clearWith,RawClearSquare.clear,Challenge.gateSlots_append]
    omega


theorem clear_resources (R : KRegs) :
    wires (clear R)⊆(wires (RawClearSquare.clear R) ∪ R.bank.toFinset) ∪ {R.S.getD (R.S.length-1) 0} ∧
    (GatePhysical (RawClearSquare.clear R) → GatePhysical (clear R)) ∧
    measurementCount (clear R)=measurementCount (RawClearSquare.clear R) ∧
    Challenge.gateSlots (clear R)≤Challenge.gateSlots (RawClearSquare.clear R) := by
  exact clearWith_resources R (DI4Merge.safe R) (DI4Merge.safe_resources R)

end ECDSAAdd.Entrant.DI4Square

namespace ECDSAAdd.Entrant.DI4Square
open Arithmetic DiagSq KRegs
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def Active (R : KRegs) : Prop :=
  diagShape R.lo R.dlo R.carry R.cin ∧ diagShape R.hi R.dhi R.carry R.cin
instance (R : KRegs) : Decidable (Active R) := inferInstanceAs (Decidable (_ ∧ _))

theorem diagSafe_tc (xs dst carry : List Wire) (cin : Wire) (h : diagShape xs dst carry cin) :
    toffoliCount (diagSafe xs dst carry cin)+1=toffoliCount (dAddZ2 xs dst carry cin) := by
  rw [diagSafe,if_pos h]
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,ht,_,_⟩ := h
  exact ht

theorem clearC_delta (R : KRegs) (h : Active R) (hm : DI4Merge.Active R) (hc7 : DI4LastCarry.Active R) :
    toffoliCount (clearC R)+5=toffoliCount (LowZero18Diagonal.clearC R) := by
  have c7 := DI4LastCarry.forR_tc R hc7
  have cm := DI4Merge.safe_tc R hm
  have l := diagSafe_tc R.lo R.dlo R.carry R.cin h.1
  have h := diagSafe_tc R.hi R.dhi R.carry R.cin h.2
  simp only [clearC,LowZero18Diagonal.clearC,RawClearSquare.clearC,clear,clearWith,RawClearSquare.clear,toffoliCount_append]
  omega

end ECDSAAdd.Entrant.DI4Square

namespace ECDSAAdd.Entrant.DI4Square
open Arithmetic KRegs
set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem clearWith_support (R : KRegs) (w : R.W) (front : Program)
    (c : wires front⊆wires R.c8g ∪ R.bank.toFinset ∧
      (GatePhysical R.c8g → GatePhysical front) ∧
      measurementCount front=measurementCount R.c8g ∧
      Challenge.gateSlots front≤Challenge.gateSlots R.c8g) :
    wires (clearWith R front)⊆R.all.toFinset := by
  apply (clearWith_resources R front c).1.trans
  apply Finset.union_subset
  · apply Finset.union_subset (RawClearSquare.clear_support R w)
    intro q hq
    have qb : q∈R.bank := List.mem_toFinset.mp hq
    simp only [KRegs.all,List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc]
    exact Or.inr (Or.inl qb)
  · intro q hq
    simp only [Finset.mem_singleton] at hq
    subst q
    have hsl : 1≤R.S.length := by have := w.S; have := w.hh; have := w.h4; omega
    have hm := RawClearCarryIntegration.getD_mem R.S (R.S.length-1) (by omega)
    simp only [KRegs.all,List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc]
    exact Or.inr (Or.inr (Or.inr (Or.inl hm)))

theorem clear_support (R : KRegs) (w : R.W) : wires (clear R)⊆R.all.toFinset := by
  exact clearWith_support R w (DI4Merge.safe R) (DI4Merge.safe_resources R)

end ECDSAAdd.Entrant.DI4Square

namespace ECDSAAdd.Entrant.DI4Square
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.measurementCount Challenge.gateSlots

theorem clearC_measurements (Q : KRegs) :
    measurementCount (clearC Q)=measurementCount (LowZero18Diagonal.clearC Q) := by
  simp only [clearC,LowZero18Diagonal.clearC,RawClearSquare.clearC,measurementCount_append,
    (clear_resources Q).2.2.1]

theorem clearC_slots (Q : KRegs) :
    Challenge.gateSlots (clearC Q)≤Challenge.gateSlots (LowZero18Diagonal.clearC Q) := by
  have h := (clear_resources Q).2.2.2
  simp only [clearC,LowZero18Diagonal.clearC,RawClearSquare.clearC,Challenge.gateSlots_append]
  omega
end ECDSAAdd.Entrant.DI4Square


end

/-! # Split 65-bit Karatsuba leaves for the concrete square -/

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic

namespace ECDSAAdd.Entrant.PaddedCarry
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Preserve all five surrounding Clifford operations and remove only the CCX. -/
def zeroMaj (a b ci c : Wire) : Program :=
  [.CX a b,.CX a ci,.CX a c,.CX a ci,.CX a b]

theorem zeroMaj_eq (a b ci c : Wire) (hn : [a,b,ci,c].Nodup)
    (s : State) (m : List Bool) (ha : s.basis a=false)
    (hc : carryBit (s.basis a) (s.basis b) (s.basis ci)=false) :
    run (zeroMaj a b ci c) m s=run (majority a b ci c) m s := by
  rw [majority_correct _ _ _ _ hn]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hab,haci,hac⟩,⟨hbci,hbc⟩,hcic⟩ := hn
  rw [ha] at hc
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq:q=c
  · subst q; simp [zeroMaj,run,writeBit,Function.update,ha,hc,hab,haci,hac,hbci,hbc,hcic,Ne.symm hab,Ne.symm haci,Ne.symm hac,Ne.symm hbci,Ne.symm hbc,Ne.symm hcic]
  · by_cases hqb:q=b <;> by_cases hqci:q=ci <;> simp_all [zeroMaj,run,writeBit,Function.update,ha,hc,hq,hab,haci,hac,hbci,hbc,hcic,Ne.symm hab,Ne.symm haci,Ne.symm hac,Ne.symm hbci,Ne.symm hbc,Ne.symm hcic]

def cut : Nat → List Wire → List Wire → List Wire → Wire → Program
  | 0,a::a'::as,b::b'::bs,c::cs,ci =>
      zeroMaj a b ci c ++ addInPlace (a'::as) (b'::bs) cs c ++ eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | k+1,a::a'::as,b::b'::bs,c::cs,ci =>
      majority a b ci c ++ cut k (a'::as) (b'::bs) cs c ++ eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | _,x,y,cs,ci => addInPlace x y cs ci

def Ready : Nat → List Wire → List Wire → Bool → BasisState → Prop
  | 0,a::a'::as,b::b'::bs,ci,s => s a=false ∧ carryBit (s a) (s b) ci=false
  | k+1,a::a'::as,b::b'::bs,ci,s => Ready k (a'::as) (b'::bs) (carryBit (s a) (s b) ci) s
  | _,_,_,_,_ => True

theorem ready_congr (k : Nat) (x y : List Wire) (ci : Bool) (s t : BasisState)
    (h : ∀q∈x++y,s q=t q) : Ready k x y ci s ↔ Ready k x y ci t := by
  induction k generalizing x y ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> try rfl
    simp only [Ready,h a (by simp),h b (by simp)]
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> try rfl
    simp only [Ready,h a (by simp),h b (by simp)]
    exact ih _ _ _ (fun q hq => h q (by simp at hq ⊢; tauto))

theorem cut_mc (k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (cut k x y cs ci)=measurementCount (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp [cut,zeroMaj,addInPlace,measurementCount_append,majority,measurementCount]
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp [cut,addInPlace,measurementCount_append,ih]

theorem cut_eq (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hok : Ready k x y (s.basis ci) s.basis) :
    run (cut k x y cs ci) m s = run (addInPlace x y cs ci) m s := by
  induction k generalizing x y cs ci s m with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try rfl
    have hcnt := List.nodup_iff_count.mp hn
    have h4 : [a,b,ci,c].Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
    have hac : a' ≠ c := by
      intro e; have := hcnt c; subst e
      simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at this; omega
    have hbc : b' ≠ c := by
      intro e; have := hcnt c; subst e
      simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at this; omega
    have hmid : run (zeroMaj a b ci c) [] s=run (majority a b ci c) [] s := by
      exact zeroMaj_eq a b ci c h4 s [] hok.1 hok.2
    simp only [cut,addInPlace,List.append_assoc]
    exact TopCarry.run_head_congr _ _ _ m s (by rfl) (by rfl) hmid
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try rfl
    have hcnt := List.nodup_iff_count.mp hn
    have h4 : [a,b,ci,c].Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    have cn := (List.nodup_cons.mp hnd').1
    have notc (q : Wire) (hq : q∈(a'::as)++(b'::bs)) : q≠c := by
      intro e; subst e; exact cn (List.mem_append_left _ hq)
    have hc0 := hclean c (by simp)
    let u : State := ⟨s.phase,writeBit s.basis c (carryBit (s.basis a) (s.basis b) (s.basis ci))⟩
    have hmaj : run (majority a b ci c) [] s=u := by
      rw [majority_correct _ _ _ _ h4]; simp [u,hc0]
    have uc : u.basis c=carryBit (s.basis a) (s.basis b) (s.basis ci) := by simp [u,writeBit]
    have uk (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,Function.update,hq]
    have okIn : Ready k (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,ready_congr k _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq))]
      exact hok
    have cleanIn : ∀q∈cs,u.basis q=false := by
      intro q hq
      have hqc : q≠c := by intro e; subst e; exact cn (List.mem_append_right _ hq)
      rw [uk q hqc]; exact hclean q (by simp [hq])
    simp only [cut,addInPlace]
    have he := TopCarry.run_mid_congr (majority a b ci c) (cut k (a'::as) (b'::bs) cs c)
      (addInPlace (a'::as) (b'::bs) cs c) (eraseCarry a b ci c ++ [.CX a b,.CX ci b]) m s
      (by rfl) (cut_mc k _ _ cs c) (fun record => by
        rw [hmaj]
        exact ih _ _ cs c hnd' u record cleanIn okIn)
    simpa only [List.append_assoc] using he


theorem zeroMaj_mc (a b ci c : Wire) : measurementCount (zeroMaj a b ci c)=0 := rfl
theorem zeroMaj_tc (a b ci c : Wire) : toffoliCount (zeroMaj a b ci c)=0 := rfl

theorem cut_tc (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) (hk : k+2≤y.length) :
    toffoliCount (cut k x y cs ci)+1=toffoliCount (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    simp only [cut,addInPlace,toffoliCount_append,show toffoliCount (zeroMaj a b ci c)=0 from rfl,majority,toffoliCount]
    omega
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    have h := ih (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [cut,addInPlace,toffoliCount_append]
    omega

def pair  : Nat → List Wire → List Wire → List Wire → Wire → Program
  | 0,a::a'::as,b::b'::bs,c::cs,ci =>
      zeroMaj a b ci c ++ cut 0 (a'::as) (b'::bs) cs c ++ eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | k+1,a::a'::as,b::b'::bs,c::cs,ci =>
      majority a b ci c ++ pair k (a'::as) (b'::bs) cs c ++ eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | _,x,y,cs,ci => addInPlace x y cs ci

theorem pair_mc  (k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (pair k x y cs ci)=measurementCount (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp [pair,addInPlace,measurementCount_append,zeroMaj_mc,cut_mc,majority,measurementCount,zeroMaj]
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp [pair,addInPlace,measurementCount_append,ih]

theorem pair_tc  (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) (hk : k+3≤y.length) :
    toffoliCount (pair k x y cs ci)+2=toffoliCount (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    have h := cut_tc 0 (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [pair,addInPlace,toffoliCount_append,zeroMaj_tc,majority,toffoliCount]
    omega
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    have h := ih (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [pair,addInPlace,toffoliCount_append]
    omega

theorem pair_eq  (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hok : Ready k x y (s.basis ci) s.basis) (hok2 : Ready (k+1) x y (s.basis ci) s.basis) :
    run (pair k x y cs ci) m s = run (addInPlace x y cs ci) m s := by
  induction k generalizing x y cs ci s m with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try rfl
    have hcnt := List.nodup_iff_count.mp hn
    have h4 : [a,b,ci,c].Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    have cn := (List.nodup_cons.mp hnd').1
    have notc (q : Wire) (hq : q∈(a'::as)++(b'::bs)) : q≠c := by
      intro e; subst e; exact cn (List.mem_append_left _ hq)
    have hc0 := hclean c (by simp)
    let u : State := ⟨s.phase,writeBit s.basis c (carryBit (s.basis a) (s.basis b) (s.basis ci))⟩
    have hmaj : run (majority a b ci c) [] s=u := by
      rw [majority_correct _ _ _ _ h4]; simp [u,hc0]
    have haff : run (zeroMaj a b ci c) [] s=u := by
      rw [zeroMaj_eq a b ci c h4 s [] hok.1 hok.2,hmaj]
    have uc : u.basis c=carryBit (s.basis a) (s.basis b) (s.basis ci) := by simp [u,writeBit]
    have uk (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,Function.update,hq]
    have okIn2 : Ready 0 (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,ready_congr 0 _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq))]
      exact hok2
    have cleanIn : ∀q∈cs,u.basis q=false := by
      intro q hq
      have hqc : q≠c := by intro e; subst e; exact cn (List.mem_append_right _ hq)
      rw [uk q hqc]; exact hclean q (by simp [hq])
    simp only [pair,addInPlace,List.append_assoc]
    rw [run_append (zeroMaj _ _ _ _),run_append (majority _ _ _ _),zeroMaj_mc,
      show measurementCount (majority a b ci c)=0 from rfl,List.take_zero,List.drop_zero,haff,hmaj]
    rw [run_append,run_append,cut_mc,cut_eq 0 _ _ cs c hnd' u _ cleanIn okIn2]
    simp only [run_append]
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try rfl
    have hcnt := List.nodup_iff_count.mp hn
    have h4 : [a,b,ci,c].Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    have cn := (List.nodup_cons.mp hnd').1
    have notc (q : Wire) (hq : q∈(a'::as)++(b'::bs)) : q≠c := by
      intro e; subst e; exact cn (List.mem_append_left _ hq)
    have hc0 := hclean c (by simp)
    let u : State := ⟨s.phase,writeBit s.basis c (carryBit (s.basis a) (s.basis b) (s.basis ci))⟩
    have hmaj : run (majority a b ci c) [] s=u := by
      rw [majority_correct _ _ _ _ h4]; simp [u,hc0]
    have uc : u.basis c=carryBit (s.basis a) (s.basis b) (s.basis ci) := by simp [u,writeBit]
    have uk (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,Function.update,hq]
    have okIn : Ready k (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,ready_congr k _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq))]
      exact hok
    have okIn2 : Ready (k+1) (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,ready_congr (k+1) _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq))]
      exact hok2
    have cleanIn : ∀q∈cs,u.basis q=false := by
      intro q hq
      have hqc : q≠c := by intro e; subst e; exact cn (List.mem_append_right _ hq)
      rw [uk q hqc]; exact hclean q (by simp [hq])
    simp only [pair,addInPlace]
    have he := TopCarry.run_mid_congr (majority a b ci c) (pair k (a'::as) (b'::bs) cs c)
      (addInPlace (a'::as) (b'::bs) cs c) (eraseCarry a b ci c ++ [.CX a b,.CX ci b]) m s
      (by rfl) (pair_mc k _ _ cs c) (fun record => by
        rw [hmaj]
        exact ih _ _ cs c hnd' u record cleanIn okIn okIn2)
    simpa only [List.append_assoc] using he


def low0 (k : Nat) (x y cs : List Wire) (ci : Wire) : Program :=
  pair k x.tail y.tail cs.tail ci ++ [.measureX (cs.headD 0) [] []]

def lowNC (k : Nat) (x y cs : List Wire) (ci : Wire) : Program :=
  low0 k x y cs ci ++ [.CX (x.headD 0) (y.headD 0),.CX ci (y.headD 0)]

def sub (k : Nat) (x y cs : List Wire) (ci : Wire) : Program :=
  notRegister y ++ lowNC k x y cs ci ++ notRegister y

theorem low0_mc (k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (low0 k x y cs ci)=measurementCount (LowZero.addLow0 x y cs ci) := by
  simp only [low0,LowZero.addLow0,measurementCount_append,pair_mc]

theorem lowNC_mc (k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (lowNC k x y cs ci)=measurementCount (LowZero.addLowNC x y cs ci) := by
  simp only [lowNC,LowZero.addLowNC,LowZero.addLow0,measurementCount_append,low0_mc]

theorem sub_mc (k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (sub k x y cs ci)=measurementCount (LowZero.subLowNC x y cs ci) := by
  simp only [sub,LowZero.subLowNC,measurementCount_append,lowNC_mc]

theorem low0_eq (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,s.basis q=false) (hok : Ready k x.tail y.tail (s.basis ci) s.basis)
    (hok2 : Ready (k+1) x.tail y.tail (s.basis ci) s.basis) :
    run (low0 k x y cs ci) m s=run (LowZero.addLow0 x y cs ci) m s := by
  simp only [low0,LowZero.addLow0,run_append,pair_mc,pair_eq k _ _ _ ci hn s _ hclean hok hok2]

theorem lowNC_eq (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,s.basis q=false) (hok : Ready k x.tail y.tail (s.basis ci) s.basis)
    (hok2 : Ready (k+1) x.tail y.tail (s.basis ci) s.basis) :
    run (lowNC k x y cs ci) m s=run (LowZero.addLowNC x y cs ci) m s := by
  change run (low0 k x y cs ci ++ _) m s=run (LowZero.addLow0 x y cs ci ++ _) m s
  rw [run_append,run_append,low0_mc,low0_eq k _ _ _ ci hn s _ hclean hok hok2]

theorem sub_eq (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,(run (notRegister y) [] s).basis q=false) (hok : Ready k x.tail y.tail ((run (notRegister y) [] s).basis ci) (run (notRegister y) [] s).basis)
    (hok2 : Ready (k+1) x.tail y.tail ((run (notRegister y) [] s).basis ci) (run (notRegister y) [] s).basis) :
    run (sub k x y cs ci) m s=run (LowZero.subLowNC x y cs ci) m s := by
  have he := TopCarry.run_mid_congr (notRegister y) (lowNC k x y cs ci)
    (LowZero.addLowNC x y cs ci) (notRegister y) m s (notRegister_counts y).2
    (lowNC_mc k x y cs ci) (fun record => lowNC_eq k x y cs ci hn _ record hclean hok hok2)
  exact he

theorem low_counts (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.tail.length=y.tail.length) (hc : cs.tail.length+1=y.tail.length) (hk : k+3≤y.tail.length) :
    toffoliCount (low0 k x y cs ci)+2=toffoliCount (LowZero.addLow0 x y cs ci) ∧
    toffoliCount (lowNC k x y cs ci)+2=toffoliCount (LowZero.addLowNC x y cs ci) ∧
    toffoliCount (sub k x y cs ci)+2=toffoliCount (LowZero.subLowNC x y cs ci) := by
  have h := pair_tc k x.tail y.tail cs.tail ci hx hc hk
  simp only [low0,lowNC,sub,LowZero.addLow0,LowZero.addLowNC,LowZero.subLowNC,toffoliCount_append]
  omega


theorem zeroMaj_sublist (a b ci c : Wire) :
    List.Sublist (zeroMaj a b ci c) (majority a b ci c) := by
  unfold zeroMaj majority
  exact List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.Sublist.cons _ (List.Sublist.refl _)))

theorem cut_sublist (k : Nat) (x y cs : List Wire) (ci : Wire) :
    List.Sublist (cut k x y cs ci) (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact List.Sublist.refl _
    exact (((zeroMaj_sublist _ _ _ _).append (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact List.Sublist.refl _
    exact (((List.Sublist.refl _).append (ih _ _ _ _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem pair_sublist (k : Nat) (x y cs : List Wire) (ci : Wire) :
    List.Sublist (pair k x y cs ci) (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact List.Sublist.refl _
    exact (((zeroMaj_sublist _ _ _ _).append (cut_sublist _ _ _ _ _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact List.Sublist.refl _
    exact (((List.Sublist.refl _).append (ih _ _ _ _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem low0_sublist (k : Nat) (x y cs : List Wire) (ci : Wire) :
    List.Sublist (low0 k x y cs ci) (LowZero.addLow0 x y cs ci) :=
  (pair_sublist _ _ _ _ _).append (List.Sublist.refl _)

theorem lowNC_sublist (k : Nat) (x y cs : List Wire) (ci : Wire) :
    List.Sublist (lowNC k x y cs ci) (LowZero.addLowNC x y cs ci) :=
  (low0_sublist _ _ _ _ _).append (List.Sublist.refl _)

theorem sub_sublist (k : Nat) (x y cs : List Wire) (ci : Wire) :
    List.Sublist (sub k x y cs ci) (LowZero.subLowNC x y cs ci) :=
  ((List.Sublist.refl _).append (lowNC_sublist _ _ _ _ _)).append (List.Sublist.refl _)

theorem pair_resources (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hp : GatePhysical (addInPlace x y cs ci)) :
    GatePhysical (pair k x y cs ci) ∧ wires (pair k x y cs ci)⊆wires (addInPlace x y cs ci) ∧
    Challenge.gateSlots (pair k x y cs ci)≤Challenge.gateSlots (addInPlace x y cs ci) := by
  have h := pair_sublist k x y cs ci
  exact ⟨fun i hi => hp i (h.subset hi),Skip4.wires_mono_of_mem _ _ (fun i hi => h.subset hi),
    Skip4.slots_mono_of_sublist _ _ h⟩

/-- The source at the chosen producer and its next bit are zero, while the
next target bit agrees with the completed sum bit. -/
def High (r : Bool) : Nat → List Wire → List Wire → BasisState → Prop
  | 0,a::a'::as,b::b'::bs,s => s a=false ∧ s a'=false ∧ s b'=r
  | k+1,a::a'::as,b::b'::bs,s => High r k (a'::as) (b'::bs) s
  | _,_,_,_ => True

theorem ready_of_output (r : Bool) (k : Nat) (x y : List Wire) (ci : Bool) (s : BasisState)
    (hh : High r k x y s)
    (ho : (regValue x s+regValue y s+ci.toNat).testBit (k+1)=r) :
    Ready k x y ci s := by
  have hok := InteriorCarry.of_sum_testBit (r,none) k x y ci s (by simpa [InteriorCarry.label] using ho)
  have aux : ∀ (j : Nat) (xs ys : List Wire) (c : Bool),
      High r j xs ys s → InteriorCarry.OK (r,none) j xs ys c s → Ready j xs ys c s := by
    intro j; induction j with
    | zero =>
      intro xs ys c hh hk
      rcases xs with _|⟨a,_|⟨a',as⟩⟩ <;> rcases ys with _|⟨b,_|⟨b',bs⟩⟩ <;> try trivial
      refine ⟨hh.1,?_⟩
      simpa [InteriorCarry.OK,InteriorCarry.label,hh.2.1,hh.2.2] using hk
    | succ j hj =>
      intro xs ys c hh hk
      rcases xs with _|⟨a,_|⟨a',as⟩⟩ <;> rcases ys with _|⟨b,_|⟨b',bs⟩⟩ <;> try trivial
      exact hj _ _ _ hh hk
  exact aux k x y ci hh hok


theorem high_of_bits (r : Bool) (k : Nat) (x y : List Wire) (s : BasisState)
    (ha : s (x.getD k 0)=false) (ha' : s (x.getD (k+1) 0)=false)
    (hb : s (y.getD (k+1) 0)=r) : High r k x y s := by
  induction k generalizing x y with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> try trivial
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> try trivial
    exact ih _ _ (by simpa only [List.getD_cons_succ] using ha)
      (by simpa only [List.getD_cons_succ] using ha')
      (by simpa only [List.getD_cons_succ] using hb)

theorem wire_bit (x : List Wire) (i : Nat) (s : BasisState) (hi : i<x.length) :
    s (x.getD i 0)=(regValue x s).testBit i := by
  have he := regValue_bit x i 0 s hi
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases hs:s (x.getD i 0) <;> simp_all

theorem bit_false_of_lt (X i : Nat) (h : X<2^i) : X.testBit i=false := by
  rw [Nat.testBit_eq_decide_div_mod_eq,Nat.div_eq_of_lt h]
  decide

theorem ready_of_small (k : Nat) (x y : List Wire) (ci : Bool) (s : BasisState)
    (hx : k+1<x.length) (hy : k+1<y.length)
    (hX : regValue x s<2^k) (hY : regValue y s<2^(k+1))
    (hS : regValue x s+regValue y s+ci.toNat<2^(k+1)) : Ready k x y ci s := by
  apply ready_of_output false
  · apply high_of_bits
    · rw [wire_bit x k s (by omega)]; exact bit_false_of_lt _ _ hX
    · rw [wire_bit x (k+1) s hx]; exact bit_false_of_lt _ _ (by rw [pow_succ]; omega)
    · rw [wire_bit y (k+1) s hy]; exact bit_false_of_lt _ _ hY
  · exact bit_false_of_lt _ _ hS

theorem pair_eq_small (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hx : k+2<x.length) (hy : k+2<y.length)
    (hX : regValue x s.basis<2^k)
    (hS : regValue x s.basis+regValue y s.basis+(s.basis ci).toNat<2^(k+1)) :
    run (pair k x y cs ci) m s=run (addInPlace x y cs ci) m s := by
  apply pair_eq k x y cs ci hn s m hclean
  · exact ready_of_small k x y _ _ (by omega) (by omega) hX (by omega) hS
  · apply ready_of_small (k+1) x y _ _ (by omega) (by omega)
    · rw [pow_succ]; omega
    · rw [show k+1+1=k+2 from by omega,pow_succ]; omega
    · rw [show k+1+1=k+2 from by omega,pow_succ]; omega


/-- Numerical boundary for both padded merge directions: the source has zero
high three bits, and adding it does not change the upper two target bits. -/
theorem pair_eq_boundary (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hx : k+2<x.length) (hy : k+2<y.length)
    (hX : regValue x s.basis<2^k)
    (hB1 : (regValue x s.basis+regValue y s.basis+(s.basis ci).toNat).testBit (k+1)=
      (regValue y s.basis).testBit (k+1))
    (hB2 : (regValue x s.basis+regValue y s.basis+(s.basis ci).toNat).testBit (k+2)=
      (regValue y s.basis).testBit (k+2)) :
    run (pair k x y cs ci) m s=run (addInPlace x y cs ci) m s := by
  apply pair_eq k x y cs ci hn s m hclean
  · apply ready_of_output ((regValue y s.basis).testBit (k+1))
    · apply high_of_bits
      · rw [wire_bit x k s.basis (by omega)]; exact bit_false_of_lt _ _ hX
      · rw [wire_bit x (k+1) s.basis (by omega)]; exact bit_false_of_lt _ _ (by rw [pow_succ]; omega)
      · exact wire_bit y (k+1) s.basis (by omega)
    · exact hB1
  · apply ready_of_output ((regValue y s.basis).testBit (k+2))
    · apply high_of_bits
      · rw [wire_bit x (k+1) s.basis (by omega)]; exact bit_false_of_lt _ _ (by rw [pow_succ]; omega)
      · rw [wire_bit x (k+1+1) s.basis (by omega)]; exact bit_false_of_lt _ _ (by rw [pow_succ,pow_succ]; omega)
      · simpa only [Nat.add_assoc] using wire_bit y (k+2) s.basis (by omega)
    · simpa only [Nat.add_assoc] using hB2


theorem regValue_tail (xs : List Wire) (s : BasisState) : regValue xs.tail s=regValue xs s/2 := by
  cases xs with
  | nil => simp [regValue]
  | cons a as =>
    change regValue as s=((if s a then 1 else 0)+2*regValue as s)/2
    cases s a <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega

theorem small_merge_eq (x y cs : List Wire) (ci : Wire)
    (hx : x.length=99) (hy : y.length=99)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,s.basis q=false) (hi : s.basis ci=false)
    (hX : regValue x s.basis<2^68)
    (hS : regValue x s.basis+regValue y s.basis<2^97) :
    run (low0 95 x y cs ci) m s=run (LowZero.addLow0 x y cs ci) m s := by
  have X : regValue x.tail s.basis<2^95 := by rw [regValue_tail]; norm_num at hX ⊢; omega
  have Y : regValue y.tail s.basis<2^96 := by rw [regValue_tail]; norm_num at hS ⊢; omega
  have S : regValue x.tail s.basis+regValue y.tail s.basis+(s.basis ci).toNat<2^96 := by
    rw [regValue_tail,regValue_tail,hi]; norm_num at hS ⊢; omega
  have xl : 97<x.tail.length := by simp [List.length_tail,hx]
  have yl : 97<y.tail.length := by simp [List.length_tail,hy]
  apply low0_eq 95 x y cs ci hn s m hclean
  · exact ready_of_small 95 x.tail y.tail _ _ (by omega) (by omega) X Y S
  · apply ready_of_small 96 x.tail y.tail _ _ (by omega) (by omega)
    · norm_num at X ⊢; omega
    · norm_num at Y ⊢; omega
    · norm_num at S ⊢; omega

private theorem upper_bit1 (X : Nat) (hL : 3*2^96≤X) (hU : X<2^98) : X.testBit 96=true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hd : X/2^96=3 := by norm_num at hL hU ⊢; omega
  rw [hd]; decide

private theorem upper_bit2 (X : Nat) (hL : 3*2^96≤X) (hU : X<2^98) : X.testBit 97=true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hd : X/2^97=1 := by norm_num at hL hU ⊢; omega
  rw [hd]; decide

/-- The complemented subtraction boundary: source is small, top target bits
are 11, and the addition has no overflow. -/
theorem upper_merge_pair_eq (x y cs : List Wire) (ci : Wire)
    (hx : x.length=98) (hy : y.length=98)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hi : s.basis ci=false)
    (hX : regValue x s.basis<2^95) (hY : 3*2^96≤regValue y s.basis)
    (hS : regValue x s.basis+regValue y s.basis<2^98) :
    run (pair 95 x y cs ci) m s=run (addInPlace x y cs ci) m s := by
  apply pair_eq_boundary 95 x y cs ci hn s m hclean (by omega) (by omega) hX
  · rw [hi]; simp only [Bool.toNat_false,Nat.add_zero]
    rw [upper_bit1 _ (by omega) hS,upper_bit1 _ hY (by omega)]
  · rw [hi]; simp only [Bool.toNat_false,Nat.add_zero]
    rw [upper_bit2 _ (by omega) hS,upper_bit2 _ hY (by omega)]


theorem upper_merge_lowNC_eq (x y cs : List Wire) (ci : Wire)
    (hx : x.length=99) (hy : y.length=99)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,s.basis q=false) (hi : s.basis ci=false)
    (hX : regValue x.tail s.basis<2^95) (hY : 3*2^96≤regValue y.tail s.basis)
    (hS : regValue x.tail s.basis+regValue y.tail s.basis<2^98) :
    run (lowNC 95 x y cs ci) m s=run (LowZero.addLowNC x y cs ci) m s := by
  have eq0 (record : List Bool) : run (low0 95 x y cs ci) record s=run (LowZero.addLow0 x y cs ci) record s := by
    simp only [low0,LowZero.addLow0,run_append,pair_mc]
    rw [upper_merge_pair_eq x.tail y.tail cs.tail ci (by simp [List.length_tail,hx])
      (by simp [List.length_tail,hy]) hn s _ hclean hi hX hY hS]
  change run (low0 95 x y cs ci ++ _) m s=run (LowZero.addLow0 x y cs ci ++ _) m s
  rw [run_append,run_append,low0_mc,eq0]

theorem small_unmerge_eq (x y cs : List Wire) (ci : Wire)
    (hx : x.length=99) (hy : y.length=99)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hi : s.basis ci=false)
    (hX : regValue x s.basis<2^68) (hY : regValue y s.basis<2^97)
    (hXY : regValue x s.basis≤regValue y s.basis) :
    run (sub 95 x y cs ci) m s=run (LowZero.subLowNC x y cs ci) m s := by
  have hc := List.nodup_iff_count.mp hn
  have yN : y.Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have := hc q
    simp only [List.count_cons,List.count_append] at this; omega
  have off (q : Wire) (hq : q∈ci::(x++cs)) : q∉y := by
    intro hqy
    have H := hc q
    have Hq := List.count_pos_iff.mpr hq
    have Hy := List.count_pos_iff.mpr hqy
    simp only [List.count_cons,List.count_append] at H Hq; omega
  let u := run (notRegister y) [] s
  have us (q : Wire) (hq : q∉y) : u.basis q=s.basis q := by
    simp [u,notRegister_correct y yN s [],hq]
  have ux : regValue x.tail u.basis=regValue x.tail s.basis := by
    apply regValue_congr; intro q hq
    exact us q (off q (by simp only [List.mem_cons,List.mem_append]; exact Or.inr (Or.inl (List.mem_of_mem_tail hq))))
  have uy : regValue y.tail u.basis=2^98-1-regValue y.tail s.basis := by
    have e : regValue y.tail u.basis=regValue y.tail (fun q => !s.basis q) := by
      apply regValue_congr; intro q hq
      simp [u,notRegister_correct y yN s [],List.mem_of_mem_tail hq]
    rw [e,regValue_complement,List.length_tail,hy]
  have ui : u.basis ci=false := (us ci (off ci (by simp))).trans hi
  have uc : ∀q∈cs.tail,u.basis q=false := by
    intro q hq
    rw [us q (off q (by simp only [List.mem_cons,List.mem_append]; exact Or.inr (Or.inr (List.mem_of_mem_tail hq))))]
    exact hclean q (List.mem_of_mem_tail hq)
  have nd : (ci::(x.tail++y.tail++cs.tail)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have H := hc q
    have X := (List.tail_sublist x).count_le q
    have Y := (List.tail_sublist y).count_le q
    have C := (List.tail_sublist cs).count_le q
    simp only [List.count_cons,List.count_append] at H ⊢; omega
  have X : regValue x.tail u.basis<2^95 := by rw [ux,regValue_tail]; norm_num at hX ⊢; omega
  have Y : 3*2^96≤regValue y.tail u.basis := by rw [uy,regValue_tail]; norm_num at hY ⊢; omega
  have S : regValue x.tail u.basis+regValue y.tail u.basis<2^98 := by
    rw [ux,uy,regValue_tail,regValue_tail]; norm_num at hX hY ⊢; omega
  exact TopCarry.run_mid_congr (notRegister y) (lowNC 95 x y cs ci)
    (LowZero.addLowNC x y cs ci) (notRegister y) m s (notRegister_counts y).2
    (lowNC_mc 95 x y cs ci) (fun record => upper_merge_lowNC_eq x y cs ci hx hy nd u record uc ui X Y S)


theorem low0_resources (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hp : GatePhysical (LowZero.addLow0 x y cs ci)) :
    GatePhysical (low0 k x y cs ci) ∧ wires (low0 k x y cs ci)⊆wires (LowZero.addLow0 x y cs ci) ∧
    Challenge.gateSlots (low0 k x y cs ci)≤Challenge.gateSlots (LowZero.addLow0 x y cs ci) := by
  have h := low0_sublist k x y cs ci
  exact ⟨fun i hi => hp i (h.subset hi),Skip4.wires_mono_of_mem _ _ (fun i hi => h.subset hi),
    Skip4.slots_mono_of_sublist _ _ h⟩

theorem sub_resources (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hp : GatePhysical (LowZero.subLowNC x y cs ci)) :
    GatePhysical (sub k x y cs ci) ∧ wires (sub k x y cs ci)⊆wires (LowZero.subLowNC x y cs ci) ∧
    Challenge.gateSlots (sub k x y cs ci)≤Challenge.gateSlots (LowZero.subLowNC x y cs ci) := by
  have h := sub_sublist k x y cs ci
  exact ⟨fun i hi => hp i (h.subset hi),Skip4.wires_mono_of_mem _ _ (fun i hi => h.subset hi),
    Skip4.slots_mono_of_sublist _ _ h⟩


theorem zeroMaj_slots (a b ci c : Wire) : Challenge.gateSlots (zeroMaj a b ci c)=5 := rfl
theorem majority_slots (a b ci c : Wire) : Challenge.gateSlots (majority a b ci c)=6 := rfl

theorem cut_slots (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) (hk : k+2≤y.length) :
    Challenge.gateSlots (cut k x y cs ci)+1=Challenge.gateSlots (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    simp only [cut,addInPlace,Challenge.gateSlots_append,zeroMaj_slots,majority_slots]
    omega
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    have h := ih (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [cut,addInPlace,Challenge.gateSlots_append]
    omega

theorem pair_slots  (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) (hk : k+3≤y.length) :
    Challenge.gateSlots (pair k x y cs ci)+2=Challenge.gateSlots (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    have h := cut_slots 0 (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [pair,addInPlace,Challenge.gateSlots_append,zeroMaj_slots,majority_slots]
    omega
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hk <;> try omega
    have h := ih (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [pair,addInPlace,Challenge.gateSlots_append]
    omega

theorem low_slots (k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.tail.length=y.tail.length) (hc : cs.tail.length+1=y.tail.length) (hk : k+3≤y.tail.length) :
    Challenge.gateSlots (low0 k x y cs ci)+2=Challenge.gateSlots (LowZero.addLow0 x y cs ci) ∧
    Challenge.gateSlots (sub k x y cs ci)+2=Challenge.gateSlots (LowZero.subLowNC x y cs ci) := by
  have h := pair_slots k x.tail y.tail cs.tail ci hx hc hk
  simp only [low0,lowNC,sub,LowZero.addLow0,LowZero.addLowNC,LowZero.subLowNC,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.PaddedCarry

namespace ECDSAAdd.Entrant.PaddedCarry
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def makeMerge (R : KRegs) : Program :=
  if R.h=33 ∧ R.bank.length=66 then
    low0 95 (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
  else R.m8g

def clearMerge (R : KRegs) : Program :=
  if R.h=33 ∧ R.bank.length=66 then
    sub 95 (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
  else R.c8g

theorem merge_lens (R : KRegs) (w : R.W) (h33 : R.h=33) (h66 : R.bank.length=66) :
    (R.T++R.zM).length=99 ∧ R.dmid.length=99 ∧
    (R.carry.take (R.dmid.length-1)).length=98 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have l := R.m8g_lens w
  exact ⟨by omega,by omega,by omega⟩

theorem merge_nodup (R : KRegs) (hn : R.all.Nodup) :
    (R.cin::((R.T++R.zM)++R.dmid++R.carry.take (R.dmid.length-1))).Nodup := by
  exact knd hn (fun q => by
    have c := R.counts q
    simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢
    omega)

theorem makeMerge_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (h33 : R.h=33) (h66 : R.bank.length=66) (s : State) (m : List Bool)
    (hclean : ∀q∈R.carry,s.basis q=false) (hi : s.basis R.cin=false)
    (hX : regValue (R.T++R.zM) s.basis<2^68)
    (hS : regValue (R.T++R.zM) s.basis+regValue R.dmid s.basis<2^97) :
    run (makeMerge R) m s=run R.m8g m s := by
  have l := merge_lens R w h33 h66
  have old := R.m8g_lens w
  have nd := merge_nodup R hn
  have ndt : (R.cin::((R.T++R.zM).tail++R.dmid.tail++(R.carry.take (R.dmid.length-1)).tail)).Nodup := by
    exact List.Nodup.sublist (List.Sublist.cons₂ _ (((List.tail_sublist _).append (List.tail_sublist _)).append (List.tail_sublist _))) nd
  simp only [makeMerge,if_pos (show R.h=33 ∧ R.bank.length=66 from ⟨h33,h66⟩),KRegs.m8g,
    LowZero.addLow0G_eq _ _ _ _ old.1 old.2.1 old.2.2]
  exact small_merge_eq _ _ _ _ l.1 l.2.1 ndt s m
    (fun q hq => hclean q (List.mem_of_mem_take (List.mem_of_mem_tail hq))) hi hX hS

theorem clearMerge_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (h33 : R.h=33) (h66 : R.bank.length=66) (s : State) (m : List Bool)
    (hclean : ∀q∈R.carry,s.basis q=false) (hi : s.basis R.cin=false)
    (hX : regValue (R.T++R.zM) s.basis<2^68)
    (hY : regValue R.dmid s.basis<2^97)
    (hXY : regValue (R.T++R.zM) s.basis≤regValue R.dmid s.basis) :
    run (clearMerge R) m s=run R.c8g m s := by
  have l := merge_lens R w h33 h66
  have old := R.m8g_lens w
  simp only [clearMerge,if_pos (show R.h=33 ∧ R.bank.length=66 from ⟨h33,h66⟩),KRegs.c8g,
    LowZero.subLowNCG_eq _ _ _ _ old.1 old.2.1 old.2.2]
  exact small_unmerge_eq _ _ _ _ l.1 l.2.1 (merge_nodup R hn) s m
    (fun q hq => hclean q (List.mem_of_mem_take hq)) hi hX hY hXY


theorem makeMerge_resources (R : KRegs) (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (makeMerge R) ∧ wires (makeMerge R)⊆wires R.m8g ∧
    measurementCount (makeMerge R)=measurementCount R.m8g ∧
    Challenge.gateSlots (makeMerge R)≤Challenge.gateSlots R.m8g := by
  have old := R.m8g_lens w
  have he : R.m8g=LowZero.addLow0 (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin := by
    exact LowZero.addLow0G_eq _ _ _ _ old.1 old.2.1 old.2.2
  unfold makeMerge; split
  · rw [he]
    have hp := R.m8g_physical hn
    rw [he] at hp
    have h := low0_resources 95 _ _ _ _ hp
    exact ⟨h.1,h.2.1,low0_mc _ _ _ _ _,h.2.2⟩
  · exact ⟨R.m8g_physical hn,Finset.Subset.refl _,rfl,Nat.le_refl _⟩

theorem clearMerge_resources (R : KRegs) (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (clearMerge R) ∧ wires (clearMerge R)⊆wires R.c8g ∧
    measurementCount (clearMerge R)=measurementCount R.c8g ∧
    Challenge.gateSlots (clearMerge R)≤Challenge.gateSlots R.c8g := by
  have old := R.m8g_lens w
  have he : R.c8g=LowZero.subLowNC (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin := by
    exact LowZero.subLowNCG_eq _ _ _ _ old.1 old.2.1 old.2.2
  unfold clearMerge; split
  · rw [he]
    have hp := R.c8g_physical hn
    rw [he] at hp
    have h := sub_resources 95 _ _ _ _ hp
    exact ⟨h.1,h.2.1,sub_mc _ _ _ _ _,h.2.2⟩
  · exact ⟨R.c8g_physical hn,Finset.Subset.refl _,rfl,Nat.le_refl _⟩

theorem merge_deltas (R : KRegs) (w : R.W) (h33 : R.h=33) (h66 : R.bank.length=66) :
    toffoliCount (makeMerge R)+2=toffoliCount R.m8g ∧
    toffoliCount (clearMerge R)+2=toffoliCount R.c8g ∧
    Challenge.gateSlots (makeMerge R)+2=Challenge.gateSlots R.m8g ∧
    Challenge.gateSlots (clearMerge R)+2=Challenge.gateSlots R.c8g := by
  have l := merge_lens R w h33 h66
  have old := R.m8g_lens w
  have x : (R.T++R.zM).tail.length=98 := by simp [List.length_tail,l.1]
  have y : R.dmid.tail.length=98 := by simp [List.length_tail,l.2.1]
  have c : (R.carry.take (R.dmid.length-1)).tail.length=97 := by simp [List.length_tail,l.2.2]
  have ht := low_counts 95 (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by omega) (by omega) (by omega)
  have hs := low_slots 95 (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by omega) (by omega) (by omega)
  simp only [makeMerge,clearMerge,if_pos (show R.h=33 ∧ R.bank.length=66 from ⟨h33,h66⟩),KRegs.m8g,KRegs.c8g,
    LowZero.addLow0G_eq _ _ _ _ old.1 old.2.1 old.2.2,
    LowZero.subLowNCG_eq _ _ _ _ old.1 old.2.1 old.2.2]
  exact ⟨ht.1,ht.2.2,hs.1,hs.2⟩

end ECDSAAdd.Entrant.PaddedCarry

namespace ECDSAAdd.Entrant.PaddedCarry
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unnecessarySimpa false

/-- Arithmetic boundaries admitted by the padded 66-bit leaf. -/
theorem padded_boundaries (a b : Nat) (ha : a<2^33) (hb : b<2^32) :
    2*a*b<2^68 ∧
    2*a*b+(a^2+2^66*b^2)/2^33=(a+2^33*b)^2/2^33 ∧
    (a+2^33*b)^2/2^33<2^97 ∧
    2*a*b≤(a+2^33*b)^2/2^33 := by
  have mul : a*b≤(2^33)*(2^32) := Nat.mul_le_mul (by omega) (by omega)
  have cross : 2*a*b<2^68 := by rw [Nat.mul_assoc]; norm_num at mul ⊢; omega
  have input : a+2^33*b<2^65 := by norm_num at ha hb ⊢; omega
  have sq := square_bound (a+2^33*b) 65 input
  have identity : (a+2^33*b)^2=(a^2+2^66*b^2)+(2*a*b)*2^33 := by ring
  have hp : 0<2^33 := by norm_num
  have div : (a+2^33*b)^2/2^33=2*a*b+(a^2+2^66*b^2)/2^33 := by
    rw [identity,Nat.add_mul_div_right _ _ hp,Nat.add_comm]
  have small : (a+2^33*b)^2/2^33<2^97 := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    norm_num at sq ⊢
    exact sq
  exact ⟨cross,div.symm,small,by rw [div]; omega⟩

theorem square_mod4 (b : Nat) : (b*b)%4=b%2 := by
  have hh : b%4<4 := Nat.mod_lt _ (by decide)
  have he : (b*b)%4=((b%4)*(b%4))%4 := Nat.mul_mod _ _ _
  interval_cases hr : b%4 <;> norm_num at he <;> omega

theorem partial_bits (h a b : Nat) (_hh : 1≤h) (ha : a<2^h) :
    (((a+2^h*b)^2/2^h-2*a*b).testBit h=b.testBit 0) ∧
    (((a+2^h*b)^2/2^h-2*a*b).testBit (h+1)=false) := by
  let P := 2^h
  have hp : 0<P := Nat.two_pow_pos _
  have aq : a^2/P<P := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    dsimp only [P]
    nlinarith
  have ex : (a+P*b)^2=a^2+P*(P*b^2+2*a*b) := by ring
  have exd : (a+P*b)^2/P=a^2/P+(P*b^2+2*a*b) := by
    rw [ex,Nat.add_mul_div_left _ _ hp]
  have ed : ((a+P*b)^2/P-2*a*b)/P=b^2 := by
    rw [exd,show a^2/P+(P*b^2+2*a*b)-2*a*b=a^2/P+P*b^2 by rw [← Nat.add_assoc,Nat.add_sub_cancel],
      Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt aq,Nat.zero_add]
  constructor
  · rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq]
    change decide ((((a+P*b)^2/P-2*a*b)/P)%2=1)=decide (b/1%2=1)
    rw [ed,Nat.div_one]
    have hm := square_mod4 b
    have hdiv := Nat.mod_add_div (b*b) 4
    have sq2 : (b*b)%2=b%2 := by omega
    simpa only [pow_two,sq2]
  · rw [Nat.testBit_eq_decide_div_mod_eq,show 2^(h+1)=P*2 by dsimp only [P]; rw [pow_succ],← Nat.div_div_eq_div_mul]
    change decide (((((a+P*b)^2/P-2*a*b)/P)/2)%2=1)=false
    rw [ed]
    have hm := square_mod4 b
    have hb : b%2<2 := Nat.mod_lt _ (by decide)
    have hdiv := Nat.mod_add_div (b*b) 4
    simp only [pow_two] at *
    have hz : (b*b)/2%2=0 := by omega
    simp [hz]
end ECDSAAdd.Entrant.PaddedCarry

namespace ECDSAAdd.Entrant.PaddedCombined
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Second affine low carry, followed by a distant pair of high zero cuts. -/
def second (v : Bool) (d : Nat) : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as,b::b'::bs,c::cs,ci =>
      InteriorCarry.affine (v,none) a' b' c ++ PaddedCarry.pair d (a'::as) (b'::bs) cs c ++
        eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | x,y,cs,ci => PaddedCarry.pair (d+1) x y cs ci

def pair (r : Bool × Option Wire) (v : Bool) (d : Nat) : Nat → List Wire → List Wire → List Wire → Wire → Program
  | 0,a::a'::as,b::b'::bs,c::cs,ci =>
      InteriorCarry.affine r a' b' c ++ second v d (a'::as) (b'::bs) cs c ++
        eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | k+1,a::a'::as,b::b'::bs,c::cs,ci =>
      majority a b ci c ++ pair r v d k (a'::as) (b'::bs) cs c ++
        eraseCarry a b ci c ++ [.CX a b,.CX ci b]
  | k,x,y,cs,ci => PaddedCarry.pair (k+d+2) x y cs ci

theorem second_mc (v : Bool) (d : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (second v d x y cs ci)=measurementCount (addInPlace x y cs ci) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
    rcases cs with _|⟨c,cs⟩ <;>
    simp [second,addInPlace,measurementCount_append,InteriorCarry.affine_mc,PaddedCarry.pair_mc,majority,measurementCount]

theorem pair_mc (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (pair r v d k x y cs ci)=measurementCount (addInPlace x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;>
      simp [pair,addInPlace,measurementCount_append,InteriorCarry.affine_mc,second_mc,PaddedCarry.pair_mc,majority,measurementCount]
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;>
      simp [pair,addInPlace,measurementCount_append,ih,PaddedCarry.pair_mc]

theorem second_eq (v : Bool) (d : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hok : InteriorCarry.OK (v,none) 0 x y (s.basis ci) s.basis) :
    run (second v d x y cs ci) m s=run (PaddedCarry.pair (d+1) x y cs ci) m s := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
    rcases cs with _|⟨c,cs⟩ <;> try rfl
  have hcnt := List.nodup_iff_count.mp hn
  have h4 : [a,b,ci,c].Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have := hcnt q
    simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
  have hac : a'≠c := by
    intro e; have := hcnt c; subst e
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at this; omega
  have hbc : b'≠c := by
    intro e; have := hcnt c; subst e
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at this; omega
  have he : run (InteriorCarry.affine (v,none) a' b' c) [] s=run (majority a b ci c) [] s := by
    rw [InteriorCarry.affine_run _ _ _ c s hac hbc (by simp),majority_correct _ _ _ _ h4]
    congr 2
    exact congrArg (fun z => s.basis c ^^ z) hok.symm
  simp only [second,PaddedCarry.pair,List.append_assoc]
  exact TopCarry.run_head_congr _ _ _ m s (InteriorCarry.affine_mc _ _ _ _) (by rfl) he

theorem low_eq (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hr : ∀q∈r.2,q∉cs)
    (hok : InteriorCarry.OK r k x y (s.basis ci) s.basis) (hok2 : InteriorCarry.OK (v,none) (k+1) x y (s.basis ci) s.basis) :
    run (pair r v d k x y cs ci) m s = run (PaddedCarry.pair (k+d+2) x y cs ci) m s := by
  induction k generalizing x y cs ci s m with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try rfl
    have hcnt := List.nodup_iff_count.mp hn
    have h4 : [a,b,ci,c].Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    have cn := (List.nodup_cons.mp hnd').1
    have notc (q : Wire) (hq : q∈(a'::as)++(b'::bs)) : q≠c := by
      intro e; subst e; exact cn (List.mem_append_left _ hq)
    have hc0 := hclean c (by simp)
    let u : State := ⟨s.phase,writeBit s.basis c (carryBit (s.basis a) (s.basis b) (s.basis ci))⟩
    have hmaj : run (majority a b ci c) [] s=u := by
      rw [majority_correct _ _ _ _ h4]; simp [u,hc0]
    have haff : run (InteriorCarry.affine r a' b' c) [] s=u := by
      rw [InteriorCarry.affine_run r _ _ c s (notc a' (by simp)) (notc b' (by simp))
        (by intro q hq e; subst e; exact hr q hq (by simp))]
      simp only [u]
      congr 2
      simpa only [hc0,Bool.false_xor] using hok.symm
    have uc : u.basis c=carryBit (s.basis a) (s.basis b) (s.basis ci) := by simp [u,writeBit]
    have uk (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,Function.update,hq]
    have okIn2 : InteriorCarry.OK (v,none) 0 (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,InteriorCarry.OK_congr (v,none) 0 _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq)) rfl]
      exact hok2
    have cleanIn : ∀q∈cs,u.basis q=false := by
      intro q hq
      have hqc : q≠c := by intro e; subst e; exact cn (List.mem_append_right _ hq)
      rw [uk q hqc]; exact hclean q (by simp [hq])
    simp only [pair,Nat.zero_add,PaddedCarry.pair,List.append_assoc]
    rw [run_append (InteriorCarry.affine _ _ _ _),run_append (majority _ _ _ _),InteriorCarry.affine_mc,
      show measurementCount (majority a b ci c)=0 from rfl,List.take_zero,List.drop_zero,haff,hmaj]
    exact TopCarry.run_mid_congr [] (second v d (a'::as) (b'::bs) cs c)
      (PaddedCarry.pair (d+1) (a'::as) (b'::bs) cs c)
      (eraseCarry a b ci c ++ [.CX a b,.CX ci b]) m u (by rfl)
      (by rw [second_mc,PaddedCarry.pair_mc])
      (fun record => second_eq v d _ _ cs c hnd' u record okIn2)
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try rfl
    have hcnt := List.nodup_iff_count.mp hn
    have h4 : [a,b,ci,c].Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append,List.count_nil] at this ⊢; omega
    have hnd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro q; have := hcnt q
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    have cn := (List.nodup_cons.mp hnd').1
    have notc (q : Wire) (hq : q∈(a'::as)++(b'::bs)) : q≠c := by
      intro e; subst e; exact cn (List.mem_append_left _ hq)
    have hc0 := hclean c (by simp)
    let u : State := ⟨s.phase,writeBit s.basis c (carryBit (s.basis a) (s.basis b) (s.basis ci))⟩
    have hmaj : run (majority a b ci c) [] s=u := by
      rw [majority_correct _ _ _ _ h4]; simp [u,hc0]
    have uc : u.basis c=carryBit (s.basis a) (s.basis b) (s.basis ci) := by simp [u,writeBit]
    have uk (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,Function.update,hq]
    have hr' : ∀q∈r.2,q∉cs := fun q hq h => hr q hq (by simp [h])
    have hlabel : InteriorCarry.label r u.basis=InteriorCarry.label r s.basis := by
      unfold InteriorCarry.label
      congr 1
      cases he : r.2 with
      | none => rfl
      | some q =>
        apply uk
        intro e; subst e; exact hr q (by rw [he]; simp) (by simp)
    have okIn : InteriorCarry.OK r k (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,InteriorCarry.OK_congr r k _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq)) hlabel]
      exact hok
    have okIn2 : InteriorCarry.OK (v,none) (k+1) (a'::as) (b'::bs) (u.basis c) u.basis := by
      rw [uc,InteriorCarry.OK_congr (v,none) (k+1) _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq)) rfl]
      exact hok2
    have cleanIn : ∀q∈cs,u.basis q=false := by
      intro q hq
      have hqc : q≠c := by intro e; subst e; exact cn (List.mem_append_right _ hq)
      rw [uk q hqc]; exact hclean q (by simp [hq])
    rw [show k+1+d+2=(k+d+2)+1 by omega]
    simp only [pair,PaddedCarry.pair]
    have he := TopCarry.run_mid_congr (majority a b ci c) (pair r v d k (a'::as) (b'::bs) cs c)
      (PaddedCarry.pair (k+d+2) (a'::as) (b'::bs) cs c) (eraseCarry a b ci c ++ [.CX a b,.CX ci b]) m s
      (by rfl) (by rw [pair_mc,PaddedCarry.pair_mc]) (fun record => by
        rw [hmaj]
        exact ih _ _ cs c hnd' u record cleanIn hr' okIn okIn2)
    simpa only [List.append_assoc] using he



theorem second_sublist (v : Bool) (d : Nat) (x y cs : List Wire) (ci : Wire) :
    List.Sublist (second v d x y cs ci) (InteriorCarry.add (v,none) 0 x y cs ci) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
    rcases cs with _|⟨c,cs⟩ <;> try exact PaddedCarry.pair_sublist _ _ _ _ _
  exact (((List.Sublist.refl _).append (PaddedCarry.pair_sublist _ _ _ _ _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem pair_sublist (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire) :
    List.Sublist (pair r v d k x y cs ci) (InteriorCarry.pair r v k x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact PaddedCarry.pair_sublist _ _ _ _ _
    exact (((List.Sublist.refl _).append (second_sublist _ _ _ _ _ _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> try exact PaddedCarry.pair_sublist _ _ _ _ _
    exact (((List.Sublist.refl _).append (ih _ _ _ _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem second_tc (v : Bool) (d : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) (hh : d+4≤y.length) :
    toffoliCount (second v d x y cs ci)+2=toffoliCount (InteriorCarry.add (v,none) 0 x y cs ci) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
    rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hh <;> try omega
  have h := PaddedCarry.pair_tc d (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
  simp only [second,InteriorCarry.add,toffoliCount_append]
  omega

theorem pair_tc (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) (hh : k+d+5≤y.length) :
    toffoliCount (pair r v d k x y cs ci)+2=toffoliCount (InteriorCarry.pair r v k x y cs ci) := by
  induction k generalizing x y cs ci with
  | zero =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hh <;> try omega
    have h := second_tc v d (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [pair,InteriorCarry.pair,toffoliCount_append]
    omega
  | succ k ih =>
    rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;>
      rcases cs with _|⟨c,cs⟩ <;> simp only [List.length_cons,List.length_nil] at hx hc hh <;> try omega
    have h := ih (a'::as) (b'::bs) cs c (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [pair,InteriorCarry.pair,toffoliCount_append]
    omega


def low0 (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire) : Program :=
  pair r v d k x.tail y.tail cs.tail ci ++ [.measureX (cs.headD 0) [] []]
def lowNC (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire) : Program :=
  low0 r v d k x y cs ci ++ [.CX (x.headD 0) (y.headD 0),.CX ci (y.headD 0)]
def sub (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire) : Program :=
  notRegister y ++ lowNC r v d k x y cs ci ++ notRegister y

theorem low0_mc (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (low0 r v d k x y cs ci)=measurementCount (PaddedCarry.low0 (k+d+2) x y cs ci) := by
  simp only [low0,PaddedCarry.low0,measurementCount_append,pair_mc,PaddedCarry.pair_mc]
theorem lowNC_mc (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (lowNC r v d k x y cs ci)=measurementCount (PaddedCarry.lowNC (k+d+2) x y cs ci) := by
  simp only [lowNC,PaddedCarry.lowNC,measurementCount_append,low0_mc]
theorem sub_mc (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire) :
    measurementCount (sub r v d k x y cs ci)=measurementCount (LowZero.subLowNC x y cs ci) := by
  simp only [sub,measurementCount_append,lowNC_mc,PaddedCarry.sub_mc,
    PaddedCarry.lowNC_mc,LowZero.subLowNC,measurementCount_append]

theorem low0_eq (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,s.basis q=false) (hr : ∀q∈r.2,q∉cs.tail)
    (hok : InteriorCarry.OK r k x.tail y.tail (s.basis ci) s.basis)
    (hok2 : InteriorCarry.OK (v,none) (k+1) x.tail y.tail (s.basis ci) s.basis) :
    run (low0 r v d k x y cs ci) m s=run (PaddedCarry.low0 (k+d+2) x y cs ci) m s := by
  simp only [low0,PaddedCarry.low0,run_append,pair_mc,PaddedCarry.pair_mc,
    low_eq r v d k _ _ _ ci hn s _ hclean hr hok hok2]

theorem lowNC_eq (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,s.basis q=false) (hr : ∀q∈r.2,q∉cs.tail)
    (hok : InteriorCarry.OK r k x.tail y.tail (s.basis ci) s.basis)
    (hok2 : InteriorCarry.OK (v,none) (k+1) x.tail y.tail (s.basis ci) s.basis) :
    run (lowNC r v d k x y cs ci) m s=run (PaddedCarry.lowNC (k+d+2) x y cs ci) m s := by
  simp only [lowNC,PaddedCarry.lowNC,run_append,low0_mc,
    low0_eq r v d k _ _ _ ci hn s _ hclean hr hok hok2]

theorem sub_eq (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire)
    (hn : (ci::(x.tail++y.tail++cs.tail)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs.tail,(run (notRegister y) [] s).basis q=false) (hr : ∀q∈r.2,q∉cs.tail)
    (hok : InteriorCarry.OK r k x.tail y.tail ((run (notRegister y) [] s).basis ci) (run (notRegister y) [] s).basis)
    (hok2 : InteriorCarry.OK (v,none) (k+1) x.tail y.tail ((run (notRegister y) [] s).basis ci) (run (notRegister y) [] s).basis) :
    run (sub r v d k x y cs ci) m s=run (PaddedCarry.sub (k+d+2) x y cs ci) m s := by
  exact TopCarry.run_mid_congr (notRegister y) (lowNC r v d k x y cs ci)
    (PaddedCarry.lowNC (k+d+2) x y cs ci) (notRegister y) m s (notRegister_counts y).2
    (lowNC_mc r v d k x y cs ci) (fun record => lowNC_eq r v d k x y cs ci hn _ record hclean hr hok hok2)

theorem sub_bits_eq (r : Bool × Option Wire) (v : Bool) (d k : Nat)
    (x y cs : List Wire) (ci : Wire) (hn : (ci::(x++y++cs)).Nodup)
    (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hr : ∀q∈r.2,q∉y ∧ q∉cs)
    (hi : s.basis ci=false) (heven : regValue x s.basis%2=0)
    (hxy : regValue x s.basis≤regValue y s.basis)
    (hk : k+3<y.length)
    (hbit : (!(regValue y s.basis-regValue x s.basis).testBit (k+2))=InteriorCarry.label r s.basis)
    (hbit2 : (!(regValue y s.basis-regValue x s.basis).testBit (k+3))=v) :
    run (sub r v d k x y cs ci) m s=run (PaddedCarry.sub (k+d+2) x y cs ci) m s := by
  have yn : y.Nodup := knd hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have nr := notRegister_correct y yn s []
  let u := run (notRegister y) [] s
  have un (q : Wire) (hq : q∉y) : u.basis q=s.basis q := by simp [u,nr,hq]
  have uy (q : Wire) (hq : q∈y) : u.basis q= !s.basis q := by simp [u,nr,hq]
  have noty (q : Wire) (hq : q∈x ∨ q∈cs ∨ q=ci) : q∉y := by
    rcases hq with hx|hc|rfl
    · exact kdis hn (fun q => by simp only [List.count_cons,List.count_append]; omega) q hx
    · exact kdis hn (fun q => by simp only [List.count_cons,List.count_append]; omega) q hc
    · exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hvx : regValue x.tail u.basis=regValue x s.basis/2 := by
    rw [regValue_congr x.tail _ s.basis (fun q hq => un q (noty q (Or.inl (List.mem_of_mem_tail hq)))),PaddedCarry.regValue_tail]
  have hvy : regValue y.tail u.basis=2^(y.length-1)-1-regValue y s.basis/2 := by
    rw [regValue_congr y.tail _ (fun q => !s.basis q) (fun q hq => uy q (List.mem_of_mem_tail hq)),
      regValue_complement,PaddedCarry.regValue_tail,List.length_tail]
  have hvci : u.basis ci=false := (un ci (noty ci (Or.inr (Or.inr rfl)))).trans hi
  have hlabel : InteriorCarry.label r u.basis=InteriorCarry.label r s.basis := by
    unfold InteriorCarry.label
    congr 1
    cases he : r.2 with
    | none => rfl
    | some q => exact un q ((hr q (by rw [he]; simp)).1)
  apply sub_eq r v d k x y cs ci (KnownTop.tail_nodup x y cs ci hn) s m
  · intro q hq
    rw [un q (noty q (Or.inr (Or.inl (List.mem_of_mem_tail hq))))]
    exact hclean q (List.mem_of_mem_tail hq)
  · intro q hq hmem
    exact (hr q hq).2 (List.mem_of_mem_tail hmem)
  · apply InteriorCarry.of_sum_testBit
    rw [hvx,hvy,hvci,Bool.toNat_false,Nat.add_zero,hlabel]
    exact (InteriorCarry.sub_tail_bit _ _ _ _ (by omega) (by omega) heven hxy (regValue_lt y s.basis)).trans hbit
  · apply InteriorCarry.of_sum_testBit
    rw [hvx,hvy,hvci,Bool.toNat_false,Nat.add_zero]
    simpa only [InteriorCarry.label,Prod.fst,Prod.snd,Option.elim_none,Bool.xor_false,Nat.add_assoc] using
      (InteriorCarry.sub_tail_bit _ _ _ _ (by omega) (by omega) heven hxy (regValue_lt y s.basis)).trans hbit2


theorem sub_sublist (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire) :
    List.Sublist (sub r v d k x y cs ci) (InteriorCarry.sub r v k x y cs ci) :=
  ((List.Sublist.refl _).append (((pair_sublist _ _ _ _ _ _ _ _).append
    (List.Sublist.refl _)).append (List.Sublist.refl _))).append (List.Sublist.refl _)

theorem sub_tc (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire)
    (hx : x.tail.length=y.tail.length) (hc : cs.tail.length+1=y.tail.length) (hh : k+d+5≤y.tail.length) :
    toffoliCount (sub r v d k x y cs ci)+2=toffoliCount (InteriorCarry.sub r v k x y cs ci) := by
  have h := pair_tc r v d k x.tail y.tail cs.tail ci hx hc hh
  simp only [sub,lowNC,low0,InteriorCarry.sub,InteriorCarry.lowNC,InteriorCarry.low0,toffoliCount_append]
  omega

theorem sub_resources (r : Bool × Option Wire) (v : Bool) (d k : Nat) (x y cs : List Wire) (ci : Wire)
    (hp : GatePhysical (InteriorCarry.sub r v k x y cs ci)) :
    GatePhysical (sub r v d k x y cs ci) ∧
    wires (sub r v d k x y cs ci)⊆wires (InteriorCarry.sub r v k x y cs ci) ∧
    Challenge.gateSlots (sub r v d k x y cs ci)≤Challenge.gateSlots (InteriorCarry.sub r v k x y cs ci) := by
  have h := sub_sublist r v d k x y cs ci
  exact ⟨fun i hi => hp i (h.subset hi),Skip4.wires_mono_of_mem _ _ (fun i hi => h.subset hi),
    Skip4.slots_mono_of_sublist _ _ h⟩

theorem sub_small_eq (r : Bool × Option Wire) (v : Bool)
    (x y cs : List Wire) (ci : Wire) (hx : x.length=99) (hy : y.length=99)
    (hn : (ci::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (hclean : ∀q∈cs,s.basis q=false) (hr : ∀q∈r.2,q∉y ∧ q∉cs)
    (hi : s.basis ci=false) (heven : regValue x s.basis%2=0)
    (hxy : regValue x s.basis≤regValue y s.basis)
    (hX : regValue x s.basis<2^68) (hY : regValue y s.basis<2^97)
    (hbit : (!(regValue y s.basis-regValue x s.basis).testBit 33)=InteriorCarry.label r s.basis)
    (hbit2 : (!(regValue y s.basis-regValue x s.basis).testBit 34)=v) :
    run (sub r v 62 31 x y cs ci) m s=run (LowZero.subLowNC x y cs ci) m s := by
  calc
    _=run (PaddedCarry.sub 95 x y cs ci) m s :=
      sub_bits_eq r v 62 31 x y cs ci hn s m hclean hr hi heven hxy (by omega) hbit hbit2
    _=_ := PaddedCarry.small_unmerge_eq x y cs ci hx hy hn s m hclean hi hX hY hxy

end ECDSAAdd.Entrant.PaddedCombined

namespace ECDSAAdd.Entrant.PaddedCombined
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def combinedMerge (R : KRegs) : Program :=
  sub (true,some (R.hi.headD 0)) true 62 31 (R.T++R.zM) R.dmid
    (R.carry.take (R.dmid.length-1)) R.cin

theorem combinedMerge_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (h33 : R.h=33) (h66 : R.bank.length=66) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0)
    (hi0 : s.basis R.cin=false) (hbank : regValue R.bank s.basis<2^65) : run (combinedMerge R) m s=run R.c8g m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have hTl := w.T; have hSl := w.S; have hCl := w.carry; have hDl := w.dst
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have ha : a<2^R.h := by simpa only [a,L0] using regValue_lt R.lo s.basis
  have zm : regValue R.zM s.basis=0 := KRegs.xz hz0 (fun q h => List.mem_of_mem_take h)
  have hX : regValue (R.T++R.zM) s.basis=2*a*b := by rw [regValue_append,hT0,zm]; simp [a,b]
  have hY : regValue R.dmid s.basis=(a+2^R.h*b)^2/2^R.h := by
    rw [show regValue R.dmid s.basis=regValue R.dst s.basis/2^R.h from
      CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by omega) s.basis,hd0,R.bank_value w]
  have hge : regValue (R.T++R.zM) s.basis≤regValue R.dmid s.basis := by
    rw [hX,hY]
    have ex : (a+2^R.h*b)^2=a^2+2^R.h*(2^R.h*b^2+2*a*b) := by ring
    rw [ex,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),← Nat.add_assoc]
    exact Nat.le_add_left _ _
  have hb : b<2^32 := by
    rw [R.bank_value w,h33] at hbank
    change a+2^33*b<2^65 at hbank
    norm_num at hbank ⊢; omega
  have bounds := PaddedCarry.padded_boundaries a b (by simpa only [h33] using ha) hb
  have Xsmall : regValue (R.T++R.zM) s.basis<2^68 := by rw [hX]; exact bounds.1
  have Ysmall : regValue R.dmid s.basis<2^97 := by rw [hY,h33]; exact bounds.2.2.1
  have lens := PaddedCarry.merge_lens R w h33 h66
  have nn : (R.cin::((R.T++R.zM)++R.dmid++R.carry.take (R.dmid.length-1))).Nodup :=
    knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have hine : R.hi≠[] := by intro e; have := congrArg List.length e; simp only [List.length_nil] at this; omega
  have hmem : R.hi.headD 0∈R.hi := by
    cases he : R.hi with
    | nil => exact False.elim (hine he)
    | cons a xs => simp
  have hlabel : s.basis (R.hi.headD 0)=b.testBit 0 := by
    have hb := LowZero.head_bit R.hi [] s.basis hine
    simpa only [List.append_nil,Nat.testBit_eq_decide_div_mod_eq,pow_zero,Nat.div_one] using hb
  have bp := PaddedCarry.partial_bits R.h a b (by omega) ha
  have e1 : R.h-2+2=R.h := by omega
  have e2 : R.h-2+3=R.h+1 := by omega
  have le := R.m8g_lens w
  rw [KRegs.c8g,LowZero.subLowNCG_eq _ _ _ _ le.1 le.2.1 le.2.2]
  unfold combinedMerge
  apply sub_small_eq _ true _ _ _ _ lens.1 lens.2.1 nn s m
  · intro q hq; exact (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq)
  · intro q hq
    simp only [Option.mem_some_iff] at hq
    subst q
    constructor
    · exact kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) _ hmem
    · exact kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) _ hmem
  · exact hi0
  · rw [hX,show 2*a*b=2*(a*b) by ring,Nat.mul_mod]
    simp
  · exact hge
  · exact Xsmall
  · exact Ysmall
  · rw [hX,hY,show 33=R.h from h33.symm,bp.1]
    simp only [InteriorCarry.label,Prod.fst,Prod.snd,Option.elim_some,hlabel,Bool.true_xor]
  · rw [hX,hY,show 34=R.h+1 from by omega,bp.2]
    rfl

def lowMerge (R : KRegs) : Program :=
  InteriorCarry.sub (true,some (R.hi.headD 0)) true 31 (R.T++R.zM) R.dmid
    (R.carry.take (R.dmid.length-1)) R.cin

theorem combinedMerge_sublist (R : KRegs) : List.Sublist (combinedMerge R) (lowMerge R) :=
  sub_sublist _ _ _ _ _ _ _ _

theorem combinedMerge_resources_low (R : KRegs) :
    wires (combinedMerge R)⊆wires (lowMerge R) ∧
    (GatePhysical (lowMerge R) → GatePhysical (combinedMerge R)) ∧
    measurementCount (combinedMerge R)=measurementCount (lowMerge R) ∧
    Challenge.gateSlots (combinedMerge R)≤Challenge.gateSlots (lowMerge R) := by
  have h := combinedMerge_sublist R
  have mc := sub_mc (true,some (R.hi.headD 0)) true 62 31 (R.T++R.zM) R.dmid
    (R.carry.take (R.dmid.length-1)) R.cin
  have oldmc := InteriorCarry.sub_mc (true,some (R.hi.headD 0)) true 31 (R.T++R.zM) R.dmid
    (R.carry.take (R.dmid.length-1)) R.cin
  exact ⟨Skip4.wires_mono_of_mem _ _ (fun i hi => h.subset hi),
    fun hp i hi => hp i (h.subset hi),mc.trans oldmc.symm,Skip4.slots_mono_of_sublist _ _ h⟩

theorem combinedMerge_tc_low (R : KRegs) (w : R.W) (h33 : R.h=33) (h66 : R.bank.length=66) :
    toffoliCount (combinedMerge R)+2=toffoliCount (lowMerge R) := by
  have lens := PaddedCarry.merge_lens R w h33 h66
  exact sub_tc _ _ _ _ _ _ _ _
    (by simp only [List.length_tail,lens.1,lens.2.1])
    (by simp only [List.length_tail]; rw [lens.2.2,lens.2.1])
    (by simp only [List.length_tail,lens.2.1]; omega)

theorem combinedMerge_tc (R : KRegs) (w : R.W) (h33 : R.h=33) (h66 : R.bank.length=66) :
    toffoliCount (combinedMerge R)+4=toffoliCount R.c8g := by
  have lens := PaddedCarry.merge_lens R w h33 h66
  have old := R.m8g_lens w
  have l := InteriorCarry.low_counts (true,some (R.hi.headD 0)) true 31 (R.T++R.zM) R.dmid
    (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_tail,lens.1,lens.2.1])
    (by simp only [List.length_tail]; rw [lens.2.2,lens.2.1])
    (by simp only [List.length_tail,lens.2.1]; omega)
  have h := combinedMerge_tc_low R w h33 h66
  change toffoliCount (combinedMerge R)+2=toffoliCount
    (InteriorCarry.sub (true,some (R.hi.headD 0)) true 31 (R.T++R.zM) R.dmid
      (R.carry.take (R.dmid.length-1)) R.cin) at h
  rw [KRegs.c8g,LowZero.subLowNCG_eq _ _ _ _ old.1 old.2.1 old.2.2]
  omega

private instance dec_instr (i : Instr) : Decidable (RecordedQuantum.PhysicalInstr (.gate i)) := by
  cases i <;> simp only [RecordedQuantum.PhysicalInstr,ProperGate] <;> infer_instance
private instance dec_physical (P : Program) : Decidable (GatePhysical P) := by
  unfold GatePhysical
  infer_instance

def Active (R : KRegs) : Prop :=
  wires (combinedMerge R)⊆wires R.c8g ∪ R.bank.toFinset ∧
  GatePhysical (combinedMerge R) ∧
  toffoliCount (combinedMerge R)+4=toffoliCount R.c8g ∧
  measurementCount (combinedMerge R)=measurementCount R.c8g ∧
  Challenge.gateSlots (combinedMerge R)≤Challenge.gateSlots R.c8g
theorem active_of_low (R : KRegs) (w : R.W) (h33 : R.h=33) (h66 : R.bank.length=66)
    (hw : wires (lowMerge R)⊆wires R.c8g ∪ R.bank.toFinset)
    (hp : GatePhysical (lowMerge R))
    (hm : measurementCount (lowMerge R)=measurementCount R.c8g)
    (hs : Challenge.gateSlots (lowMerge R)≤Challenge.gateSlots R.c8g) : Active R := by
  have h := combinedMerge_resources_low R
  exact ⟨h.1.trans hw,h.2.1 hp,combinedMerge_tc R w h33 h66,h.2.2.1.trans hm,h.2.2.2.trans hs⟩

instance (R : KRegs) : Decidable (Active R) := inferInstanceAs (Decidable (_ ∧ _))

def safe (R : KRegs) : Program := if Active R then combinedMerge R else R.c8g

theorem safe_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (h33 : R.h=33) (h66 : R.bank.length=66) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0)
    (hi0 : s.basis R.cin=false) (hbank : regValue R.bank s.basis<2^65) :
    run (safe R) m s=run R.c8g m s := by
  by_cases h : Active R
  · rw [safe,if_pos h]
    exact combinedMerge_eq R w hn h33 h66 s m hd0 hT0 hz0 hc0 hi0 hbank
  · rw [safe,if_neg h]

theorem safe_resources (R : KRegs) :
    wires (safe R)⊆wires R.c8g ∪ R.bank.toFinset ∧
    (GatePhysical R.c8g → GatePhysical (safe R)) ∧
    measurementCount (safe R)=measurementCount R.c8g ∧
    Challenge.gateSlots (safe R)≤Challenge.gateSlots R.c8g := by
  by_cases h : Active R
  · rw [safe,if_pos h]
    exact ⟨h.1,fun _ => h.2.1,h.2.2.2.1,h.2.2.2.2⟩
  · rw [safe,if_neg h]
    exact ⟨Finset.subset_union_left,id,rfl,le_refl _⟩

theorem safe_tc (R : KRegs) (h : Active R) : toffoliCount (safe R)+4=toffoliCount R.c8g := by
  rw [safe,if_pos h]
  exact h.2.2.1

end ECDSAAdd.Entrant.PaddedCombined

namespace ECDSAAdd.Entrant.PaddedCombined
open Arithmetic
set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem active_of_merge (R : KRegs) (w : R.W) (h33 : R.h=33) (h66 : R.bank.length=66)
    (h : DI4Merge.Active R) : Active R := by
  have he : lowMerge R=DI4Merge.merge R := by simp only [lowMerge,DI4Merge.merge,h33]
  have r := combinedMerge_resources_low R
  rw [he] at r
  exact ⟨r.1.trans h.1,r.2.1 h.2.1,combinedMerge_tc R w h33 h66,
    r.2.2.1.trans h.2.2.2.1,r.2.2.2.trans h.2.2.2.2⟩
end ECDSAAdd.Entrant.PaddedCombined

namespace ECDSAAdd.Entrant.DI4PadClear
open ECDSAAdd Arithmetic DiagSq KRegs
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def clear (R : KRegs) : Program := DI4Square.clearWith R (PaddedCombined.safe R)
def clearC (R : KRegs) : Program := R.smkT++clear R

theorem clear_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (h33 : R.h=33) (h66 : R.bank.length=66)
    (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false)
    (hbank : regValue R.bank s.basis<2^65) :
    (run (clear R) m s).phase=s.phase ∧
    regValue R.dst (run (clear R) m s).basis=0 ∧
    regValue R.S (run (clear R) m s).basis=0 ∧
    regValue R.T (run (clear R) m s).basis=0 ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (clear R) m s).basis q=s.basis q := by
  exact DI4Square.clearWith_correct R (PaddedCombined.safe R) w he (Or.inr h33) hn s m
    hd0 hS0 hT0 hz0 hp0 hc0 hi0
    (fun r => PaddedCombined.safe_eq R w hn h33 h66 s r hd0 hT0 hz0 hc0 hi0 hbank)

variable (R : KRegs)
theorem cl_spec (w : R.W) (he : R.bank.length=2*R.h) (h33 : R.h=33) (h66 : R.bank.length=66) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    ∀ (s : State) (m : List Bool),
    regValue R.dst s.basis=(regValue R.bank s.basis)^2 → R.invC (regValue R.bank s.basis) s.basis →
    regValue R.pad s.basis=0 → regValue R.carry s.basis=0 → regValue z s.basis=0 →
    s.basis R.cin=false → regValue R.bank s.basis<2^65 →
    (run (clearC R) m s).phase=s.phase ∧ regValue R.dst (run (clearC R) m s).basis=0 ∧
    regValue (R.S++R.T) (run (clearC R) m s).basis=0 ∧
    ∀q,q∉R.dst → q∉R.S++R.T → (run (clearC R) m s).basis q=s.basis q := by
  intro s m hd0 hI hp0 hc0 hz0 hi0 hbank
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
  have c := clear_correct R w he h33 h66 hn u b (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),bk]; exact hd0)
    (by rw [r.2.1,lo,hi])
    (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))),hI.2,lo,hi,R.lo_mod w,R.hi_div w])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inl h))))).trans hp0)
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((r.2.2 _ (o _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).trans hi0)
    (by rw [bk]; exact hbank)
  have eq : run (clearC R) m s=run (clear R) b u := by
    rw [clearC,run_append,(R.smkT_counts w).2,
      R.smkT_run w hn s _ (by rw [hI.2,R.lo_mod w,R.hi_div w]) hI.1 hi0,←hu]
  rw [eq]
  refine ⟨c.1.trans r.1,c.2.1,?_,?_⟩
  · rw [regValue_append,c.2.2.1,c.2.2.2.1]; simp
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2.2.2 q h xS xT).trans (r.2.2 q xS)


end ECDSAAdd.Entrant.DI4PadClear

namespace ECDSAAdd.Entrant.DI4PadClear
open ECDSAAdd Arithmetic DiagSq KRegs
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical

theorem clearC_clean (Q : KRegs) (w : Q.W) (he : Q.bank.length = 2 * Q.h) (h33 : Q.h=33) (h66 : Q.bank.length=66)
    (hn : Q.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue Q.dst s.basis = (regValue Q.bank s.basis) ^ 2)
    (hS0 : regValue Q.S s.basis = 0)
    (hT0 : regValue Q.T s.basis = 2 * regValue Q.lo s.basis * regValue Q.hi s.basis)
    (hz0 : regValue Q.z s.basis = 0) (hp0 : regValue Q.pad s.basis = 0)
    (hc0 : regValue Q.carry s.basis = 0) (hi0 : s.basis Q.cin = false)
    (hbank : regValue Q.bank s.basis<2^65) :
    (run (clearC Q) m s).phase = s.phase ∧
    regValue Q.dst (run (clearC Q) m s).basis = 0 ∧
    regValue Q.T (run (clearC Q) m s).basis = 0 ∧
    ∀ q, q ∉ Q.dst → q ∉ Q.T → (run (clearC Q) m s).basis q = s.basis q := by
  have hI : Q.invC (regValue Q.bank s.basis) s.basis := by
    refine ⟨hS0, ?_⟩
    rw [hT0, Q.lo_mod w, Q.hi_div w]
  have r := cl_spec Q w he h33 h66 hn Q.z (fun _ h => h) s m hd0 hI hp0 hc0 hz0 hi0 hbank
  have hST := (regValue_append Q.S Q.T _).symm.trans r.2.2.1
  have hST0 := Nat.add_eq_zero_iff.mp hST
  have hS1 : regValue Q.S (run (clearC Q) m s).basis = 0 := hST0.1
  have hT1 : regValue Q.T (run (clearC Q) m s).basis = 0 :=
    (Nat.mul_eq_zero.mp hST0.2).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
  refine ⟨r.1, r.2.1, hT1, ?_⟩
  intro q hd hT
  by_cases hS : q ∈ Q.S
  · exact ((regValue_zero Q.S _).mp hS1 q hS).trans ((regValue_zero Q.S _).mp hS0 q hS).symm
  · exact r.2.2.2 q hd (fun hx => (List.mem_append.mp hx).elim hS hT)


theorem clearC_support (R : KRegs) (w : R.W) : wires (clearC R)⊆R.all.toFinset := by
  rw [clearC,wires_append]
  exact Finset.union_subset (R.smkT_support w (R.piece_support w).1)
    (DI4Square.clearWith_support R w (PaddedCombined.safe R) (PaddedCombined.safe_resources R))

theorem clearC_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (clearC R) := by
  rw [clearC,gatePhysical_append]
  exact ⟨R.smkT_physical w hn (R.piece_physical hn).1,
    (DI4Square.clearWith_resources R (PaddedCombined.safe R) (PaddedCombined.safe_resources R)).2.1
      (RawClearSquare.clear_physical R w hn)⟩

theorem clearC_measurements (R : KRegs) :
    measurementCount (clearC R)=measurementCount (LowZero18Diagonal.clearC R) := by
  have h := (DI4Square.clearWith_resources R (PaddedCombined.safe R) (PaddedCombined.safe_resources R)).2.2.1
  simp only [clearC,LowZero18Diagonal.clearC,RawClearSquare.clearC,measurementCount_append,clear,h]

theorem clearC_slots (R : KRegs) :
    Challenge.gateSlots (clearC R)≤Challenge.gateSlots (LowZero18Diagonal.clearC R) := by
  have h := (DI4Square.clearWith_resources R (PaddedCombined.safe R) (PaddedCombined.safe_resources R)).2.2.2
  simp only [clearC,LowZero18Diagonal.clearC,RawClearSquare.clearC,Challenge.gateSlots_append,clear]
  omega

theorem clearC_delta (R : KRegs) (h : DI4Square.Active R)
    (hm : PaddedCombined.Active R) (hc7 : DI4LastCarry.Active R) :
    toffoliCount (clearC R)+7=toffoliCount (LowZero18Diagonal.clearC R) := by
  have cm := PaddedCombined.safe_tc R hm
  have c7 := DI4LastCarry.forR_tc R hc7
  have l := DI4Square.diagSafe_tc R.lo R.dlo R.carry R.cin h.1
  have h := DI4Square.diagSafe_tc R.hi R.dhi R.carry R.cin h.2
  simp only [clearC,LowZero18Diagonal.clearC,RawClearSquare.clearC,clear,DI4Square.clearWith,RawClearSquare.clear,toffoliCount_append]
  omega
end ECDSAAdd.Entrant.DI4PadClear

namespace ECDSAAdd.Entrant.DI4PaddedHigh
open ECDSAAdd Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def oldHead (a b y z ci c d : Wire) : Program :=
  mappedMajority ⟨some a,true⟩ y ci c ++ mappedMajority ⟨some b,true⟩ z c d

def newHead (b z c : Wire) : Program := [.CX b c,.CX z c]

def after (b z top c d : Wire) : Program :=
  [.CX d top] ++ mappedEraseCarry ⟨some b,true⟩ z c d ++ mappedSum ⟨some b,true⟩ z c

theorem keep_target (P : Program) (q : Wire)
    (h : ∀ i∈P, ZeroReadDevelop.targetOf i≠q) (s : State) (m : List Bool) :
    (run P m s).basis q=s.basis q := by
  induction P generalizing s m with
  | nil => rfl
  | cons i P ih =>
    change (run ([i]++P) m s).basis q=s.basis q
    rw [run_append,ih (fun j hj=>h j (by simp [hj]))]
    exact ZeroReadDevelop.single_target_preserves q i s _ (h i (by simp))

theorem head_summary (a b y z top ci c d : Wire)
    (hn : [a,b,y,z,top,ci,c,d].Nodup) (s : State) (m : List Bool)
    (hc : s.basis c=false) (hd : s.basis d=false) :
    run (oldHead a b y z ci c d) m s =
      ⟨s.phase,writeBit (writeBit s.basis c (carryBit (!s.basis a) (s.basis y) (s.basis ci))) d
        (carryBit (!s.basis b) (s.basis z) (carryBit (!s.basis a) (s.basis y) (s.basis ci)))⟩ := by
  have counts := List.nodup_iff_count.mp hn
  have distinct := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,not_false_eq_true,and_true] at distinct
  simp only [Wire] at *
  have n0 : [y,ci,c].Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h:=counts q
    simp only [List.count_cons,List.count_nil,beq_self_eq_true,if_true,beq_iff_eq] at h ⊢; omega
  have n1 : [z,c,d].Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h:=counts q
    simp only [List.count_cons,List.count_nil,beq_self_eq_true,if_true,beq_iff_eq] at h ⊢; omega
  have h0 : ∀q∈(some a:Option Wire),q∉[y,ci,c] := by
    intro q hq; simp only [Option.mem_some_iff] at hq; subst q
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; aesop
  have h1 : ∀q∈(some b:Option Wire),q∉[z,c,d] := by
    intro q hq; simp only [Option.mem_some_iff] at hq; subst q
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; aesop
  have ne : b≠c ∧ z≠c ∧ d≠c := by aesop
  rw [oldHead,run_append,mappedMajority_correct _ _ _ _ n0 h0,
    mappedMajority_correct _ _ _ _ n1 h1]
  simp [MappedBit.value,writeBit,Function.update,hc,hd,ne.1,ne.2.1,ne.2.2]

theorem after_bits (b z top c d : Wire) (hn : [b,z,top,c,d].Nodup)
    (s : State) (m : List Bool) :
    (run (after b z top c d) m s).basis z=(!s.basis b ^^ s.basis z ^^ s.basis c) ∧
    (run (after b z top c d) m s).basis top=(s.basis top ^^ s.basis d) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  rcases hn with ⟨⟨hbz,hbt,hbc,hbd⟩,⟨⟨hzt,hzc,hzd⟩,⟨⟨htc,htd⟩,hcd,_⟩⟩⟩
  simp [after,mappedEraseCarry,eraseBorrow,eraseCarry,mappedSum,run,measureAndCorrect,correct,
    writeBit,Function.update,hbz,hbt,hbc,hbd,hzt,hzc,hzd,htc,htd,hcd,
    Ne.symm hbz,Ne.symm hbt,Ne.symm hbc,Ne.symm hbd,Ne.symm hzt,
    Ne.symm hzc,Ne.symm hzd,Ne.symm htc,Ne.symm htd,Ne.symm hcd,
    Bool.xor_assoc,Bool.xor_comm]

theorem recover_bits (b z k l : Bool) (hz : (!b ^^ z ^^ k)=true)
    (ht : (true ^^ l)=true) : k=(b ^^ z) ∧ l=false := by
  cases b <;> cases z <;> cases k <;> cases l <;> simp_all

theorem core_head_eq (a b y z top ci c d : Wire)
    (hn : [a,b,y,z,top,ci,c,d].Nodup) (s : State) (m : List Bool)
    (hc : s.basis c=false) (hd : s.basis d=false) (ht : s.basis top=true)
    (hzOut : (run (after b z top c d) m (run (oldHead a b y z ci c d) [] s)).basis z=true)
    (htOut : (run (after b z top c d) m (run (oldHead a b y z ci c d) [] s)).basis top=true) :
    run (newHead b z c) [] s=run (oldHead a b y z ci c d) [] s := by
  have counts := List.nodup_iff_count.mp hn
  have distinct := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,not_false_eq_true,and_true] at distinct
  simp only [Wire] at *
  have nc : a≠c ∧ b≠c ∧ y≠c ∧ z≠c ∧ top≠c ∧ ci≠c ∧ d≠c := by
    aesop
  have nd : a≠d ∧ b≠d ∧ y≠d ∧ z≠d ∧ top≠d ∧ ci≠d ∧ c≠d := by
    aesop
  rcases nc with ⟨hac,hbc,hyc,hzc,htc,hic,hdc⟩
  rcases nd with ⟨had,hbd,hyd,hzd,htd,hid,hcd⟩
  have n5 : [b,z,top,c,d].Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h:=counts q
    simp only [List.count_cons,List.count_nil,beq_self_eq_true,if_true,beq_iff_eq] at h ⊢; omega
  have eM := head_summary a b y z top ci c d hn s [] hc hd
  have bits:=after_bits b z top c d n5 (run (oldHead a b y z ci c d) [] s) m
  have hz:=bits.1.symm.trans hzOut
  have htt:=bits.2.symm.trans htOut
  rw [eM] at hz htt
  simp only [writeBit,Function.update_apply,hbc,hbd,hzc,hzd,htc,htd,hdc,hcd,
    ite_false,ite_true,ht] at hz htt
  have kk:=recover_bits (s.basis b) (s.basis z)
    (carryBit (!s.basis a) (s.basis y) (s.basis ci))
    (carryBit (!s.basis b) (s.basis z) (carryBit (!s.basis a) (s.basis y) (s.basis ci))) hz htt
  rw [eM,kk.2,kk.1]
  simp only [newHead,run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hqc:q=c
  · subst q
    simp [newHead,run,writeBit,Function.update,hc,hbc,hzc,hcd]
  · by_cases hqd:q=d
    · subst q
      simp [newHead,run,writeBit,Function.update,hd,hdc,hbc,hzc]
    · simp [newHead,run,writeBit,Function.update,hqc,hqd]

theorem oldHead_mc (a b y z ci c d : Wire) : measurementCount (oldHead a b y z ci c d)=0 := by
  simp only [oldHead,measurementCount_append,
    (mappedBit_counts ⟨some a,true⟩ y ci c).2.1,
    (mappedBit_counts ⟨some b,true⟩ z c d).2.1,Nat.zero_add]

theorem recover_pair (P B : Program) (a b y z top ci c d : Wire)
    (hn : [a,b,y,z,top,ci,c,d].Nodup) (hmP : measurementCount P=0)
    (keepZ : ∀i∈B, ZeroReadDevelop.targetOf i≠z)
    (keepTop : ∀i∈B, ZeroReadDevelop.targetOf i≠top)
    (s : State) (m : List Bool)
    (hc : (run P [] s).basis c=false) (hd : (run P [] s).basis d=false)
    (ht : (run P [] s).basis top=true)
    (hzOut : (run (P++oldHead a b y z ci c d++after b z top c d++B) m s).basis z=true)
    (htOut : (run (P++oldHead a b y z ci c d++after b z top c d++B) m s).basis top=true) :
    run (P++newHead b z c++after b z top c d++B) m s=
      run (P++oldHead a b y z ci c d++after b z top c d++B) m s := by
  have hz : (run (after b z top c d) (m.take (measurementCount (after b z top c d)))
      (run (oldHead a b y z ci c d) [] (run P [] s))).basis z=true := by
    simpa only [List.append_assoc,run_append,hmP,oldHead_mc,List.take_zero,List.drop_zero,
      keep_target B z keepZ] using hzOut
  have hh : (run (after b z top c d) (m.take (measurementCount (after b z top c d)))
      (run (oldHead a b y z ci c d) [] (run P [] s))).basis top=true := by
    simpa only [List.append_assoc,run_append,hmP,oldHead_mc,List.take_zero,List.drop_zero,
      keep_target B top keepTop] using htOut
  have eq:=core_head_eq a b y z top ci c d hn (run P [] s) _ hc hd ht hz hh
  simp only [List.append_assoc,run_append,hmP,oldHead_mc,
    show measurementCount (newHead b z c)=0 from rfl,List.take_zero,List.drop_zero,eq]

end ECDSAAdd.Entrant.DI4PaddedHigh
namespace ECDSAAdd.Entrant.DI4PaddedHigh
open ECDSAAdd Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

structure MajFrame where
  bit : MappedBit
  y : Wire
  cin : Wire
  c : Wire

def MajFrame.program (a : MajFrame) : Program := mappedMajority a.bit a.y a.cin a.c

def MajFrame.Good (a : MajFrame) : Prop :=
  [a.y,a.cin,a.c].Nodup ∧ ∀q∈a.bit.wire,q∉[a.y,a.cin,a.c]
instance (a : MajFrame) : Decidable a.Good := inferInstanceAs (Decidable (_ ∧ _))

theorem MajFrame.keep (a : MajFrame) (ha : a.Good) (q : Wire) (hq : q≠a.c)
    (s : State) (m : List Bool) : (run a.program m s).basis q=s.basis q := by
  rw [MajFrame.program,mappedMajority_correct _ _ _ _ ha.1 ha.2]
  simp [writeBit,hq]

def majPrefix (xs : List MajFrame) : Program := xs.flatMap MajFrame.program

theorem majPrefix_keep (xs : List MajFrame) (q : Wire)
    (hg : ∀a∈xs,a.Good) (hq : ∀a∈xs,q≠a.c) (s : State) (m : List Bool) :
    (run (majPrefix xs) m s).basis q=s.basis q := by
  induction xs generalizing s m with
  | nil => rfl
  | cons a xs ih =>
    change (run (a.program ++ majPrefix xs) m s).basis q=s.basis q
    rw [run_append]
    rw [ih (by intros; apply hg; simp_all) (by intros; apply hq; simp_all)]
    exact a.keep (hg a (by simp)) q (hq a (by simp)) s _

theorem majPrefix_mc (xs : List MajFrame) : measurementCount (majPrefix xs)=0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [majPrefix,List.flatMap_cons,measurementCount_append,MajFrame.program,
      (mappedBit_counts a.bit a.y a.cin a.c).2.1]
    simpa only [majPrefix,Nat.zero_add] using ih

end ECDSAAdd.Entrant.DI4PaddedHigh
namespace ECDSAAdd.Entrant.DI4PaddedHigh
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def frames (xs dst cs : List Wire) : List MajFrame :=
  (List.range' 1 (2*xs.length-4)).map fun i =>
    ⟨(mappedDiagonal xs).getD i ⟨none,false⟩,dst.getD i 0,cs.getD (i-1) 0,cs.getD i 0⟩
def lead (xs dst cs : List Wire) (ci : Wire) : Program :=
  maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0) ++ majPrefix (frames xs dst cs)
def heads (xs dst cs : List Wire) : Program :=
  oldHead (xs.getD (xs.length-3) 0) (xs.getD (xs.length-2) 0)
    (dst.getD (2*xs.length-3) 0) (dst.getD (2*xs.length-2) 0)
    (cs.getD (2*xs.length-4) 0) (cs.getD (2*xs.length-3) 0) (cs.getD (2*xs.length-2) 0)
def following (xs dst cs : List Wire) : Program :=
  after (xs.getD (xs.length-2) 0) (dst.getD (2*xs.length-2) 0) (dst.getD (2*xs.length-1) 0)
    (cs.getD (2*xs.length-3) 0) (cs.getD (2*xs.length-2) 0)
def rest (xs dst cs : List Wire) (ci : Wire) : Program :=
  (dAddZ xs dst cs ci).drop ((lead xs dst cs ci).length+(heads xs dst cs).length+(following xs dst cs).length)
def inner (xs dst cs : List Wire) (ci : Wire) : Program :=
  lead xs dst cs ci ++ newHead (xs.getD (xs.length-2) 0) (dst.getD (2*xs.length-2) 0)
    (cs.getD (2*xs.length-3) 0) ++ following xs dst cs ++ rest xs dst cs ci

def program (xs dst cs : List Wire) (ci : Wire) : Program :=
  notRegister dst ++ inner xs dst cs ci ++ notRegister dst

def Shape (xs dst cs : List Wire) (ci : Wire) : Prop :=
  let n:=xs.length
  let c:=cs.getD (2*n-3) 0
  let d:=cs.getD (2*n-2) 0
  let z:=dst.getD (2*n-2) 0
  let top:=dst.getD (2*n-1) 0
  xs.length=33 ∧ dst.length=66 ∧ dst.Nodup ∧
  dAddZ xs dst cs ci=lead xs dst cs ci ++ heads xs dst cs ++ following xs dst cs ++ rest xs dst cs ci ∧
  [xs.getD (n-3) 0,xs.getD (n-2) 0,dst.getD (2*n-3) 0,z,top,cs.getD (2*n-4) 0,c,d].Nodup ∧
  c∉dst ∧ d∉dst ∧ z∈dst ∧ top∈dst ∧
  c∉wires (maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0)) ∧
  d∉wires (maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0)) ∧
  top∉wires (maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0)) ∧
  (∀a∈frames xs dst cs,a.Good) ∧
  (∀a∈frames xs dst cs,c≠a.c ∧ d≠a.c ∧ top≠a.c) ∧
  (∀i∈rest xs dst cs ci, ZeroReadDevelop.targetOf i≠z) ∧
  (∀i∈rest xs dst cs ci, ZeroReadDevelop.targetOf i≠top) ∧
  wires (program xs dst cs ci)⊆wires (dSubZ xs dst cs ci) ∧
  GatePhysical (program xs dst cs ci) ∧
  toffoliCount (program xs dst cs ci)+2=toffoliCount (dSubZ xs dst cs ci) ∧
  measurementCount (program xs dst cs ci)=measurementCount (dSubZ xs dst cs ci) ∧
  Challenge.gateSlots (program xs dst cs ci)≤Challenge.gateSlots (dSubZ xs dst cs ci)

private instance dec_instr (i : Instr) : Decidable (RecordedQuantum.PhysicalInstr (.gate i)) := by
  cases i <;> simp only [RecordedQuantum.PhysicalInstr,ProperGate] <;> infer_instance
private instance dec_physical (P : Program) : Decidable (GatePhysical P) := by
  unfold GatePhysical
  infer_instance
instance (xs dst cs : List Wire) (ci : Wire) : Decidable (Shape xs dst cs ci) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem lead_mc (xs dst cs : List Wire) (ci : Wire) : measurementCount (lead xs dst cs ci)=0 := by
  simp [lead,maj0,measurementCount_append,measurementCount,majPrefix_mc]

theorem lead_keep (xs dst cs : List Wire) (ci q : Wire)
    (hpre : q∉wires (maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0)))
    (hg : ∀a∈frames xs dst cs,a.Good) (hq : ∀a∈frames xs dst cs,q≠a.c)
    (s : State) (m : List Bool) : (run (lead xs dst cs ci) m s).basis q=s.basis q := by
  rw [lead,run_append,majPrefix_keep _ _ hg hq]
  exact run_preserves_outside _ _ _ _ hpre

theorem program_eq (xs dst cs : List Wire) (ci : Wire) (h : Shape xs dst cs ci)
    (s : State) (m : List Bool)
    (hc : s.basis (cs.getD (2*xs.length-3) 0)=false)
    (hd : s.basis (cs.getD (2*xs.length-2) 0)=false)
    (hin : s.basis (dst.getD (2*xs.length-1) 0)=false)
    (hout : (run (dSubZ xs dst cs ci) m s).basis (dst.getD (2*xs.length-2) 0)=false ∧
      (run (dSubZ xs dst cs ci) m s).basis (dst.getD (2*xs.length-1) 0)=false) :
    run (program xs dst cs ci) m s=run (dSubZ xs dst cs ci) m s := by
  obtain ⟨_hx,_hd,hdnd,he,hn,hcn,hdn,hzm,htm,hcp,hdp,htp,hg,hq,kz,kt,_hw,_hp,_ht,hm,_hs⟩ := h
  let u:=run (notRegister dst) [] s
  have un (q : Wire) : u.basis q=if q∈dst then !s.basis q else s.basis q := by
    dsimp only [u]; rw [notRegister_correct dst hdnd]
  have nr (r : List Bool) : run (notRegister dst) r s=u := by
    dsimp only [u]; rw [notRegister_correct dst hdnd,notRegister_correct dst hdnd]
  have runOld : run (dSubZ xs dst cs ci) m s=
      run (notRegister dst) (m.drop (measurementCount (dAddZ xs dst cs ci)))
        (run (dAddZ xs dst cs ci) m u) := by
    simp only [dSubZ,List.append_assoc,run_append,(notRegister_counts dst).2,
      List.take_zero,List.drop_zero,nr,run_take]
  rw [runOld,notRegister_correct dst hdnd] at hout
  simp only [hzm,htm,ite_true,Bool.not_eq_false] at hout
  have hc' : (run (lead xs dst cs ci) [] u).basis (cs.getD (2*xs.length-3) 0)=false := by
    rw [lead_keep _ _ _ _ _ hcp hg (fun a ha=>(hq a ha).1),un,if_neg hcn,hc]
  have hd' : (run (lead xs dst cs ci) [] u).basis (cs.getD (2*xs.length-2) 0)=false := by
    rw [lead_keep _ _ _ _ _ hdp hg (fun a ha=>(hq a ha).2.1),un,if_neg hdn,hd]
  have ht' : (run (lead xs dst cs ci) [] u).basis (dst.getD (2*xs.length-1) 0)=true := by
    rw [lead_keep _ _ _ _ _ htp hg (fun a ha=>(hq a ha).2.2),un,if_pos htm,hin]
    rfl
  have notFalse (b : Bool) (h : (!b)=false) : b=true := by cases b <;> simp_all
  have out0 := notFalse _ hout.1
  have out1 := notFalse _ hout.2
  rw [he] at out0 out1
  have e := recover_pair (lead xs dst cs ci) (rest xs dst cs ci)
    (xs.getD (xs.length-3) 0) (xs.getD (xs.length-2) 0)
    (dst.getD (2*xs.length-3) 0) (dst.getD (2*xs.length-2) 0) (dst.getD (2*xs.length-1) 0)
    (cs.getD (2*xs.length-4) 0) (cs.getD (2*xs.length-3) 0) (cs.getD (2*xs.length-2) 0)
    hn (lead_mc _ _ _ _) kz kt u m hc' hd' ht' out0 out1
  have eBody : run (inner xs dst cs ci) m u=run (dAddZ xs dst cs ci) m u := by
    rw [he]
    exact e
  have eMc : measurementCount (inner xs dst cs ci)=measurementCount (dAddZ xs dst cs ci) := by
    simpa only [program,dSubZ,measurementCount_append,(notRegister_counts dst).2,
      Nat.zero_add,Nat.add_zero] using hm
  have takeInner : run (inner xs dst cs ci) (m.take (measurementCount (dAddZ xs dst cs ci))) u=
      run (inner xs dst cs ci) m u := by rw [←eMc,run_take]
  simp only [program,dSubZ,List.append_assoc,run_append,(notRegister_counts dst).2,
    List.take_zero,List.drop_zero,nr,run_take,eMc,takeInner,eBody]

def safe (xs dst cs : List Wire) (ci : Wire) : Program :=
  if Shape xs dst cs ci then program xs dst cs ci else dSubZ xs dst cs ci

theorem safe_eq (xs dst cs : List Wire) (ci : Wire) (s : State) (m : List Bool)
    (hc : s.basis (cs.getD (2*xs.length-3) 0)=false)
    (hd : s.basis (cs.getD (2*xs.length-2) 0)=false)
    (hin : s.basis (dst.getD (2*xs.length-1) 0)=false)
    (hout : (run (dSubZ xs dst cs ci) m s).basis (dst.getD (2*xs.length-2) 0)=false ∧
      (run (dSubZ xs dst cs ci) m s).basis (dst.getD (2*xs.length-1) 0)=false) :
    run (safe xs dst cs ci) m s=run (dSubZ xs dst cs ci) m s := by
  by_cases h : Shape xs dst cs ci
  · rw [safe,if_pos h]; exact program_eq _ _ _ _ h s m hc hd hin hout
  · rw [safe,if_neg h]

theorem safe_resources (xs dst cs : List Wire) (ci : Wire) :
    wires (safe xs dst cs ci)⊆wires (dSubZ xs dst cs ci) ∧
    (GatePhysical (dSubZ xs dst cs ci) → GatePhysical (safe xs dst cs ci)) ∧
    measurementCount (safe xs dst cs ci)=measurementCount (dSubZ xs dst cs ci) ∧
    Challenge.gateSlots (safe xs dst cs ci)≤Challenge.gateSlots (dSubZ xs dst cs ci) := by
  by_cases h : Shape xs dst cs ci
  · have hc:=h
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hw,hp,_,hm,hs⟩:=h
    rw [safe,if_pos hc]
    exact ⟨hw,fun _=>hp,hm,hs⟩
  · rw [safe,if_neg h]
    exact ⟨Finset.Subset.refl _,id,rfl,le_refl _⟩

theorem safe_tc (xs dst cs : List Wire) (ci : Wire) (h : Shape xs dst cs ci) :
    toffoliCount (safe xs dst cs ci)+2=toffoliCount (dSubZ xs dst cs ci) := by
  have hc:=h
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,ht,_,_⟩:=h
  rw [safe,if_pos hc]
  exact ht

end ECDSAAdd.Entrant.DI4PaddedHigh
namespace ECDSAAdd.Entrant.DI4PaddedHigh
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem raw_top_aux (Q x : Nat) (hQ : 0 < Q) (hx : x < 2*Q) :
    (2*Q*Q ≤ x*x+x+(Q-1-x%Q)*(2*Q)) ↔ Q ≤ x := by
  have hv : x%Q < Q := Nat.mod_lt _ hQ
  have hd : x/Q ≤ 1 := by
    have := Nat.div_lt_of_lt_mul (show x < Q*2 by omega)
    omega
  have split := Nat.mod_add_div x Q
  obtain ⟨k,hk⟩ : ∃ k, Q = x%Q+1+k := ⟨Q-1-x%Q,by omega⟩
  have ek : Q-1-x%Q=k := by omega
  rw [ek]
  generalize x%Q=v at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hb|hb
  · rw [hb] at split
    have ex : x=v := by omega
    subst x
    constructor
    · intro h
      nlinarith [Nat.zero_le (v*k), Nat.zero_le (k*k)]
    · intro h; omega
  · rw [hb] at split
    have ex : x=v+Q := by omega
    rw [ex]
    constructor
    · omega
    · intro _
      nlinarith [Nat.zero_le (v*v),Nat.zero_le (v*k),Nat.zero_le (k*k)]

theorem raw_top (n x : Nat) (hn : 1≤n) (hx : x<2^n) :
    (2^(2*n-1) ≤ rawValue n x) ↔ 2^(n-1) ≤ x := by
  have hP : 2^n=2*2^(n-1) := KRegs.pow_two_mul_split n hn
  have hPP : 2^(2*n-1)=2*2^(n-1)*2^(n-1) := by
    have he : 2*n-1=(n-1)+(n-1)+1 := by omega
    rw [he,pow_succ,pow_add]
    ring
  unfold rawValue signedDiagValue
  rw [if_neg (by omega),hP,hPP]
  simpa only [pow_two, Nat.add_assoc] using raw_top_aux _ _ (Nat.two_pow_pos _) (by rwa [hP] at hx)


end ECDSAAdd.Entrant.DI4PaddedHigh
namespace ECDSAAdd.Entrant.DI4PaddedHigh
open ECDSAAdd Arithmetic DiagSq KRegs
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem bit_false_of_lt (xs : List Wire) (s : BasisState) (i : Nat)
    (hi : i<xs.length) (hv : regValue xs s<2^i) : s (xs.getD i 0)=false := by
  rw [RawClearCarryProbe.register_bit xs i s hi,Nat.div_eq_of_lt hv]
  rfl

theorem transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=33)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0)
    (v out : Fin 4 → Int)
    (hin : v 1=(rawValue R.h (regValue R.hi base.basis) : Nat))
    (hout : out 1=((regValue R.hi base.basis)^2 : Nat))
    (hb : regValue R.hi base.basis<2^32)
    (old : Transition R base v out (dSubZ R.hi R.dhi R.carry R.cin)) :
    Transition R base v out (safe R.hi R.dhi R.carry R.cin) := by
  intro t m ht
  have ho:=old t m ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩:=R.lens w
  have hiLen : R.hi.length=33 := by omega
  have dstLen : R.dhi.length=66 := by omega
  have rawBound : rawValue R.h (regValue R.hi base.basis)<2^65 := by
    have h:=raw_top 33 (regValue R.hi base.basis) (by decide) (by omega)
    rw [hh]
    by_contra bad
    have big : 2^65≤rawValue 33 (regValue R.hi base.basis) := by omega
    have bbig:=h.mp big
    omega
  have squareBound : (regValue R.hi base.basis)^2<2^64 := square_bound _ 32 hb
  have inputValue : regValue R.dhi t.basis=rawValue R.h (regValue R.hi base.basis) := by
    exact ht.exact 1 _ hin (by change rawValue R.h (regValue R.hi base.basis)<2^R.dhi.length; rw [dstLen]; exact lt_of_lt_of_le rawBound (by norm_num))
  have outputValue : regValue R.dhi (run (dSubZ R.hi R.dhi R.carry R.cin) m t).basis=
      (regValue R.hi base.basis)^2 := by
    exact ho.exact 1 _ hout (by change (regValue R.hi base.basis)^2<2^R.dhi.length; rw [dstLen]; exact lt_of_lt_of_le squareBound (by norm_num))
  have clean : regValue R.carry t.basis=0 :=
    (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have cl (i : Nat) (hi : i<R.carry.length) : t.basis (R.carry.getD i 0)=false :=
    (regValue_zero _ _).mp clean _ (RawClearCarryIntegration.getD_mem _ _ hi)
  have inBit : t.basis (R.dhi.getD (2*R.hi.length-1) 0)=false := by
    apply bit_false_of_lt
    · omega
    · rw [inputValue,hiLen]; exact rawBound
  have outBits : (run (dSubZ R.hi R.dhi R.carry R.cin) m t).basis (R.dhi.getD (2*R.hi.length-2) 0)=false ∧
      (run (dSubZ R.hi R.dhi R.carry R.cin) m t).basis (R.dhi.getD (2*R.hi.length-1) 0)=false := by
    constructor
    · apply bit_false_of_lt
      · omega
      · rw [outputValue,hiLen]; exact squareBound
    · apply bit_false_of_lt
      · omega
      · rw [outputValue,hiLen]; exact lt_of_lt_of_le squareBound (by norm_num)
  rw [safe_eq _ _ _ _ t m (cl _ (by have h:=w.carry; omega))
    (cl _ (by have h:=w.carry; omega)) inBit outBits]
  exact ho
end ECDSAAdd.Entrant.DI4PaddedHigh

namespace ECDSAAdd.Entrant.DI4PadMake
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- A high diagonal replacement preserves the old transition on the padded input domain. -/
def HighRefinement (R : KRegs) (high : Program) : Prop :=
  ∀(base : State), regValue R.carry base.basis=0 → ∀(v out : Fin 4 → Int),
    v 1=(rawValue R.h (regValue R.hi base.basis) : Nat) →
    out 1=((regValue R.hi base.basis)^2 : Nat) →
    regValue R.hi base.basis<2^32 →
    Transition R base v out (dSubZ R.hi R.dhi R.carry R.cin) →
    Transition R base v out high

def headWith (R : KRegs) (high : Program) : Program :=
  seedsT R ++ (R.m6w++R.m7g++corrZ2 R++dSubZ R.lo R.dlo R.carry R.cin++high)
def makeWith (R : KRegs) (high : Program) : Program :=
  headWith R high ++ PaddedCarry.makeMerge R

theorem prefixWith_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (high : Program) (hRef : HighRefinement R high) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) (hbPad : regValue R.hi s.basis<2^32) :
    Shape R s (run (headWith R high) m s)
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
  have st5New := hRef s hc0 _ _ (by simp only [vec,B,b]; rfl) (by simp only [vec,b]; rfl) hbPad st5'
  have tail := (((st1.seq st2).seq st3).seq st4').seq st5New
  have initial := seedsT_shape R w he hn s (m.take (measurementCount (seedsT R))) hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have result := tail _ (m.drop (measurementCount (seedsT R))) initial
  simpa only [headWith,run_append,A,B,S,Z,a,b,Int.natCast_mul,Int.natCast_add,Int.natCast_pow] using result


theorem makeWith_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (high : Program) (hRef : HighRefinement R high)
    (h33 : R.h=33) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) (hbPad : regValue R.hi s.basis<2^32) :
    (run (makeWith R high) m s).phase=s.phase ∧
    regValue R.dst (run (makeWith R high) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.S (run (makeWith R high) m s).basis=regValue R.lo s.basis+regValue R.hi s.basis ∧
    regValue R.T (run (makeWith R high) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (makeWith R high) m s).basis q=s.basis q := by
  have h66 : R.bank.length=66 := by omega
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let f := m.take (measurementCount (headWith R high))
  let g := m.drop (measurementCount (headWith R high))
  let u := run (headWith R high) f s
  have h := prefixWith_shape R w he hh hn high hRef s f hd0 hS0 hT0 hz0 hp0 hc0 hi0 hbPad
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
  have bd := PaddedCarry.padded_boundaries a b (by simpa only [h33] using al) hbPad
  have dm : regValue R.dmid u.basis=(a^2+2^(2*R.h)*b^2)/2^R.h := by
    rw [show regValue R.dmid u.basis=regValue R.dst u.basis/2^R.h from
      CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by have := w.dst; omega) u.basis,dv]
  have hX8 : regValue (R.T++R.zM) u.basis<2^68 := by
    rw [regValue_append,tv,zv]
    simpa only [Nat.mul_zero,Nat.add_zero] using bd.1
  have hSum8 : regValue (R.T++R.zM) u.basis+regValue R.dmid u.basis<2^97 := by
    rw [regValue_append,tv,zv,dm,h33]
    simp only [Nat.mul_zero,Nat.add_zero]
    change 2*a*b+(a^2+2^66*b^2)/2^33<2^97
    rw [bd.2.1]
    exact bd.2.2.1
  have eq8 := PaddedCarry.makeMerge_eq R w hn h33 h66 u g
    ((regValue_zero _ _).mp cv) ((h.cin hn).trans hi0) hX8 hSum8
  have em : run (makeWith R high) m s=run R.m8g g u := by
    rw [makeWith,run_append]
    exact eq8
  simpa only [em,a,b] using result

end ECDSAAdd.Entrant.DI4PadMake

namespace ECDSAAdd.Entrant.DI4PadMake
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option linter.unusedSimpArgs false

def high (R : KRegs) : Program := DI4PaddedHigh.safe R.hi R.dhi R.carry R.cin

def make (R : KRegs) : Program := makeWith R (high R)

def makeC (R : KRegs) : Program := make R ++ R.scl1591

def Active (R : KRegs) : Prop := DI4PaddedHigh.Shape R.hi R.dhi R.carry R.cin
instance (R : KRegs) : Decidable (Active R) := inferInstanceAs (Decidable (DI4PaddedHigh.Shape _ _ _ _))

theorem high_refinement (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (h33 : R.h=33) (hn : R.all.Nodup) : HighRefinement R (high R) := by
  intro base hc0 v out hin hout hb old
  exact DI4PaddedHigh.transition R w he h33 hn base hc0 v out hin hout hb old

end ECDSAAdd.Entrant.DI4PadMake

namespace ECDSAAdd.Entrant.DI4PadMake
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The padded bank bound supplies the strengthened high-half diagonal domain. -/
theorem high_lt32 (R : KRegs) (w : R.W) (h33 : R.h=33) (s : State)
    (hbank65 : regValue R.bank s.basis<2^65) : regValue R.hi s.basis<2^32 := by
  rw [R.hi_div w,h33]
  apply Nat.div_lt_of_lt_mul
  simpa only [←Nat.pow_add] using hbank65

/-- Padded producer with the sum scratch cleaned, matching the existing clean leaf frame. -/
theorem makeC_clean (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (h33 : R.h=33) (h66 : R.bank.length=66) (hn : R.all.Nodup)
    (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=0) (hS0 : regValue R.S s.basis=0)
    (hT0 : regValue R.T s.basis=0) (hz0 : regValue R.z s.basis=0)
    (hp0 : regValue R.pad s.basis=0) (hc0 : regValue R.carry s.basis=0)
    (hi0 : s.basis R.cin=false) (hbank65 : regValue R.bank s.basis<2^65) :
    (run (makeC R) m s).phase=s.phase ∧
    regValue R.dst (run (makeC R) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.T (run (makeC R) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.T → (run (makeC R) m s).basis q=s.basis q := by
  let a:=m.take (measurementCount (make R))
  let b:=m.drop (measurementCount (make R))
  have hbPad:=high_lt32 R w h33 s hbank65
  have r:=makeWith_correct R w he (Or.inr h33) hn (high R)
    (high_refinement R w he h33 hn) h33 s a hd0 hS0 hT0 hz0 hp0 hc0 hi0 hbPad
  generalize hu : run (makeWith R (high R)) a s=u at r
  have fu : ∀q,q∉R.S → q∉R.T → q∉R.dst → u.basis q=s.basis q :=
    fun q hs ht hd=>r.2.2.2.2 q hd hs ht
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S ∧ q∉R.T ∧ q∉R.dst) :
      regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq=>fu q (hl q hq).1 (hl q hq).2.1 (hl q hq).2.2)
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) :
      q∉R.S ∧ q∉R.T ∧ q∉R.dst :=
    let x:=R.outside hn q h; ⟨x.2.1,x.2.2,x.1⟩
  have lo : regValue R.lo u.basis=regValue R.lo s.basis :=
    keep _ (fun q h=>o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis :=
    keep _ (fun q h=>o q (Or.inl (List.mem_of_mem_drop h)))
  have c:=R.scl1591_correct w hn u b (by rw [r.2.2.1,lo,hi])
    ((keep _ (fun q h=>o q (Or.inr (Or.inl h)))).trans hz0)
    ((keep _ (fun q h=>o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((fu _ (o _ (by simp)).1 (o _ (by simp)).2.1 (o _ (by simp)).2.2).trans hi0)
  have eq : run (makeC R) m s=run R.scl1591 b u := by
    rw [makeC,make,run_append,←hu]
    rfl
  rw [eq]
  have dS : ∀q∈R.dst,q∉R.S := kdis hn (fun q=>by
    simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have TS : ∀q∈R.T,q∉R.S := kdis hn (fun q=>by
    simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  refine ⟨c.1.trans r.1,?_,?_,?_⟩
  · rw [kkeep c.2.2 dS,r.2.1]
  · rw [kkeep c.2.2 TS,r.2.2.2.1]
  · intro q hd ht
    by_cases hs:q∈R.S
    · exact ((regValue_zero _ _).mp c.2.1 q hs).trans ((regValue_zero _ _).mp hS0 q hs).symm
    · exact (c.2.2 q hs).trans (fu q hs ht hd)

end ECDSAAdd.Entrant.DI4PadMake

namespace ECDSAAdd.Entrant.DI4PadMake
open ECDSAAdd Arithmetic DiagSq
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- Static merge resources do not require a Nodup witness. -/
theorem makeMerge_static (R : KRegs) (w : R.W) :
    wires (PaddedCarry.makeMerge R)⊆wires R.m8g ∧
    measurementCount (PaddedCarry.makeMerge R)=measurementCount R.m8g ∧
    Challenge.gateSlots (PaddedCarry.makeMerge R)≤Challenge.gateSlots R.m8g := by
  have old := R.m8g_lens w
  have he : R.m8g=LowZero.addLow0 (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin :=
    LowZero.addLow0G_eq _ _ _ _ old.1 old.2.1 old.2.2
  unfold PaddedCarry.makeMerge; split
  · rw [he]
    have h := PaddedCarry.low0_sublist 95 (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    exact ⟨Skip4.wires_mono_of_mem _ _ (fun i hi => h.subset hi),PaddedCarry.low0_mc _ _ _ _ _,
      Skip4.slots_mono_of_sublist _ _ h⟩
  · exact ⟨Finset.Subset.refl _,rfl,le_refl _⟩

theorem makeWith_support (R : KRegs) (w : R.W) (high : Program)
    (hw : wires high⊆wires (dSubZ R.hi R.dhi R.carry R.cin)) :
    wires (makeWith R high)⊆wires (LowZero18Diagonal.make R) := by
  have hm := (makeMerge_static R w).1
  simp only [makeWith,headWith,LowZero18Diagonal.make,DiagSq.makeZ,headBlockZ,wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _) hw)) hm

theorem makeWith_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) (high : Program)
    (hp : GatePhysical (dSubZ R.hi R.dhi R.carry R.cin) → GatePhysical high) :
    GatePhysical (makeWith R high) := by
  have old := DiagSq.makeZ_physical R w hn
  simp only [DiagSq.makeZ,headBlockZ,gatePhysical_append] at old
  simp only [makeWith,headWith,gatePhysical_append]
  exact ⟨⟨old.1.1,⟨old.1.2.1,hp old.1.2.2⟩⟩,(PaddedCarry.makeMerge_resources R w hn).1⟩

theorem makeWith_measurements (R : KRegs) (w : R.W) (high : Program)
    (hm : measurementCount high=measurementCount (dSubZ R.hi R.dhi R.carry R.cin)) :
    measurementCount (makeWith R high)=measurementCount (LowZero18Diagonal.make R) := by
  have h := (makeMerge_static R w).2.1
  simp only [makeWith,headWith,LowZero18Diagonal.make,DiagSq.makeZ,headBlockZ,measurementCount_append,hm,h]

theorem makeWith_slots (R : KRegs) (w : R.W) (high : Program)
    (hs : Challenge.gateSlots high≤Challenge.gateSlots (dSubZ R.hi R.dhi R.carry R.cin)) :
    Challenge.gateSlots (makeWith R high)≤Challenge.gateSlots (LowZero18Diagonal.make R) := by
  have h := (makeMerge_static R w).2.2
  simp only [makeWith,headWith,LowZero18Diagonal.make,DiagSq.makeZ,headBlockZ,Challenge.gateSlots_append]
  omega

theorem makeWith_delta (R : KRegs) (w : R.W) (h33 : R.h=33) (h66 : R.bank.length=66)
    (high : Program) (ht : toffoliCount high+2=toffoliCount (dSubZ R.hi R.dhi R.carry R.cin)) :
    toffoliCount (makeWith R high)+4=toffoliCount (LowZero18Diagonal.make R) := by
  have h := (PaddedCarry.merge_deltas R w h33 h66).1
  simp only [makeWith,headWith,LowZero18Diagonal.make,DiagSq.makeZ,headBlockZ,toffoliCount_append]
  omega


theorem makeC_support (R : KRegs) (w : R.W) :
    wires (makeC R)⊆wires (LowZero18Diagonal.makeC R) := by
  have h := makeWith_support R w (high R)
    (DI4PaddedHigh.safe_resources R.hi R.dhi R.carry R.cin).1
  simp only [makeC,make,LowZero18Diagonal.makeC,wires_append]
  exact Finset.union_subset_union h (Finset.Subset.refl _)

theorem makeC_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeC R) := by
  simp only [makeC,gatePhysical_append]
  exact ⟨makeWith_physical R w hn (high R)
    (DI4PaddedHigh.safe_resources R.hi R.dhi R.carry R.cin).2.1,R.scl1591_physical w hn⟩

theorem makeC_measurements (R : KRegs) (w : R.W) :
    measurementCount (makeC R)=measurementCount (LowZero18Diagonal.makeC R) := by
  have h := makeWith_measurements R w (high R)
    (DI4PaddedHigh.safe_resources R.hi R.dhi R.carry R.cin).2.2.1
  simp only [makeC,make,LowZero18Diagonal.makeC,measurementCount_append]
  exact congrArg (fun k => k+measurementCount R.scl1591) h

theorem makeC_slots (R : KRegs) (w : R.W) :
    Challenge.gateSlots (makeC R)≤Challenge.gateSlots (LowZero18Diagonal.makeC R) := by
  have h := makeWith_slots R w (high R)
    (DI4PaddedHigh.safe_resources R.hi R.dhi R.carry R.cin).2.2.2
  simp only [makeC,make,LowZero18Diagonal.makeC,Challenge.gateSlots_append]
  omega

theorem makeC_delta (R : KRegs) (w : R.W) (h33 : R.h=33) (h66 : R.bank.length=66)
    (ha : Active R) : toffoliCount (makeC R)+4=toffoliCount (LowZero18Diagonal.makeC R) := by
  have hh := DI4PaddedHigh.safe_tc R.hi R.dhi R.carry R.cin ha
  have h := makeWith_delta R w h33 h66 (high R) hh
  simp only [makeC,make,LowZero18Diagonal.makeC,toffoliCount_append]
  omega

end ECDSAAdd.Entrant.DI4PadMake
namespace ECDSAAdd.Entrant.DI5DiagonalGeometry
open ECDSAAdd Arithmetic DiagSq DI4Square
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true

/-- The old ten structural fields plus two small layout facts. No whole-program
resource equalities, support subset, or physicality are decided here. -/
def Geometry (xs dst carry : List Wire) (cin : Wire) : Prop :=
  let n := xs.length
  let c := carry.getD (2*n-2) 0
  let top := dst.getD (2*n-1) 0
  let label := xs.getD (n-1) 0
  let bit : MappedBit := ⟨some (xs.getD (n-2) 0),true⟩
  let y := dst.getD (2*n-2) 0
  let ci := carry.getD (2*n-3) 0
  dAddZ2 xs dst carry cin = diagP xs dst carry cin ++ mappedMajority bit y ci c ++ [.CX c top] ++ diagB xs dst carry cin ∧
  [y,ci,c].Nodup ∧ (∀q∈bit.wire,q∉[y,ci,c]) ∧ top≠c ∧
  c∉wires (diagPre xs dst carry cin) ∧ top∉wires (diagPre xs dst carry cin) ∧
  label∉wires (diagPre xs dst carry cin) ∧
  (∀a∈diagFrames xs dst carry,a.Good) ∧
  (∀a∈diagFrames xs dst carry,c≠a.c ∧ top≠a.c ∧ label≠a.c) ∧
  top∉wires (diagB xs dst carry cin) ∧
  label∈wires (diagP xs dst carry cin) ∧ label≠c

instance (xs dst carry : List Wire) (cin : Wire) : Decidable (Geometry xs dst carry cin) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- One complemented-source majority becomes two CNOTs. Long prefix/suffix
programs stay opaque; label support is witnessed once in the shared prefix. -/
theorem replace_top_resources (P B : Program) (bitWire y ci c top label : Wire)
    (hlP : label∈wires P) (hlc : label≠c) (htc : top≠c)
    (oldPhysical : GatePhysical
      (P ++ mappedMajority ⟨some bitWire,true⟩ y ci c ++ [.CX c top] ++ B)) :
    wires (P ++ [.CX label c,.CX top c] ++ [.CX c top] ++ B) ⊆
      wires (P ++ mappedMajority ⟨some bitWire,true⟩ y ci c ++ [.CX c top] ++ B) ∧
    GatePhysical (P ++ [.CX label c,.CX top c] ++ [.CX c top] ++ B) ∧
    toffoliCount (P ++ [.CX label c,.CX top c] ++ [.CX c top] ++ B)+1 =
      toffoliCount (P ++ mappedMajority ⟨some bitWire,true⟩ y ci c ++ [.CX c top] ++ B) ∧
    measurementCount (P ++ [.CX label c,.CX top c] ++ [.CX c top] ++ B) =
      measurementCount (P ++ mappedMajority ⟨some bitWire,true⟩ y ci c ++ [.CX c top] ++ B) ∧
    Challenge.gateSlots (P ++ [.CX label c,.CX top c] ++ [.CX c top] ++ B) ≤
      Challenge.gateSlots (P ++ mappedMajority ⟨some bitWire,true⟩ y ci c ++ [.CX c top] ++ B) := by
  have support : wires [.CX label c,.CX top c] ⊆ wires P ∪ wires [.CX c top] := by
    intro q hq
    simp [wires,Instr.wires] at hq ⊢
    aesop
  have physical : GatePhysical [.CX label c,.CX top c] := by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,hlc,htc]
  have oldT : toffoliCount (mappedMajority ⟨some bitWire,true⟩ y ci c)=1 := rfl
  have newT : toffoliCount [.CX label c,.CX top c]=0 := rfl
  have oldM : measurementCount (mappedMajority ⟨some bitWire,true⟩ y ci c)=0 := rfl
  have newM : measurementCount [.CX label c,.CX top c]=0 := rfl
  have oldS : Challenge.gateSlots (mappedMajority ⟨some bitWire,true⟩ y ci c)=8 := rfl
  have newS : Challenge.gateSlots [.CX label c,.CX top c]=2 := rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro q hq
    have localSupport := @support q
    simp only [wires_append,Finset.mem_union] at hq ⊢
    simp only [Finset.mem_union] at localSupport
    tauto
  · simp only [gatePhysical_append] at oldPhysical ⊢
    tauto
  · simp only [toffoliCount_append,oldT,newT]
    omega
  · simp only [measurementCount_append,oldM,newM]
  · simp only [Challenge.gateSlots_append,oldS,newS]
    omega

/-- Reconstruct the unchanged public diagShape from geometry and imported
physicality, deriving its trailing five resource fields algebraically. -/
theorem shape_of_geometry (xs dst carry : List Wire) (cin : Wire)
    (geometry : Geometry xs dst carry cin)
    (oldPhysical : GatePhysical (dAddZ2 xs dst carry cin)) :
    diagShape xs dst carry cin := by
  obtain ⟨split,hn,ha,hct,hcp,htp,hlp,hg,hqc,htB,labelMem,labelNe⟩ := geometry
  have old : GatePhysical (diagP xs dst carry cin ++
      mappedMajority ⟨some (xs.getD (xs.length-2) 0),true⟩
        (dst.getD (2*xs.length-2) 0) (carry.getD (2*xs.length-3) 0) (carry.getD (2*xs.length-2) 0) ++
      [.CX (carry.getD (2*xs.length-2) 0) (dst.getD (2*xs.length-1) 0)] ++
      diagB xs dst carry cin) := by
    rw [←split]
    exact oldPhysical
  have resources := replace_top_resources (diagP xs dst carry cin) (diagB xs dst carry cin)
    (xs.getD (xs.length-2) 0) (dst.getD (2*xs.length-2) 0)
    (carry.getD (2*xs.length-3) 0) (carry.getD (2*xs.length-2) 0)
    (dst.getD (2*xs.length-1) 0) (xs.getD (xs.length-1) 0)
    labelMem labelNe hct old
  have result :
      wires (diagTop xs dst carry cin) ⊆ wires (dAddZ2 xs dst carry cin) ∧
      GatePhysical (diagTop xs dst carry cin) ∧
      toffoliCount (diagTop xs dst carry cin)+1=toffoliCount (dAddZ2 xs dst carry cin) ∧
      measurementCount (diagTop xs dst carry cin)=measurementCount (dAddZ2 xs dst carry cin) ∧
      Challenge.gateSlots (diagTop xs dst carry cin)≤Challenge.gateSlots (dAddZ2 xs dst carry cin) := by
    simpa only [diagTop,split] using resources
  exact ⟨split,hn,ha,hct,hcp,htp,hlp,hg,hqc,htB,
    result.1,result.2.1,result.2.2.1,result.2.2.2.1,result.2.2.2.2⟩

/-- The original clear-side physicality provides both old diagonals once.
Only Geometry remains as a concrete layout certificate. -/
theorem active_of_W_geometry (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (lo : Geometry R.lo R.dlo R.carry R.cin)
    (hi : Geometry R.hi R.dhi R.carry R.cin) : DI4Square.Active R := by
  have physical := RawClearSquare.clear_physical R w hn
  simp only [RawClearSquare.clear,gatePhysical_append] at physical
  have low : GatePhysical (dAddZ2 R.lo R.dlo R.carry R.cin) := by tauto
  have high : GatePhysical (dAddZ2 R.hi R.dhi R.carry R.cin) := by tauto
  exact ⟨shape_of_geometry _ _ _ _ lo low,shape_of_geometry _ _ _ _ hi high⟩

end ECDSAAdd.Entrant.DI5DiagonalGeometry

namespace ECDSAAdd.Entrant.DI5DiagonalGeometry
open ECDSAAdd Arithmetic DiagSq DI4Square
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true

/-- The remaining large prefix/tail Finsets are replaced by linear scans of
individual instructions. All four negative wire checks inspect one instruction at a time. -/
def CoreGeometry (xs dst carry : List Wire) (cin : Wire) : Prop :=
  let n := xs.length
  let c := carry.getD (2*n-2) 0
  let top := dst.getD (2*n-1) 0
  let label := xs.getD (n-1) 0
  let bit : MappedBit := ⟨some (xs.getD (n-2) 0),true⟩
  let y := dst.getD (2*n-2) 0
  let ci := carry.getD (2*n-3) 0
  dAddZ2 xs dst carry cin = diagP xs dst carry cin ++ mappedMajority bit y ci c ++ [.CX c top] ++ diagB xs dst carry cin ∧
  [y,ci,c].Nodup ∧ (∀q∈bit.wire,q∉[y,ci,c]) ∧ top≠c ∧
  (∀i∈diagPre xs dst carry cin,c∉i.wires) ∧
  (∀i∈diagPre xs dst carry cin,top∉i.wires) ∧
  (∀i∈diagPre xs dst carry cin,label∉i.wires) ∧
  (∀a∈diagFrames xs dst carry,a.Good) ∧
  (∀a∈diagFrames xs dst carry,c≠a.c ∧ top≠a.c ∧ label≠a.c) ∧
  (∀i∈diagB xs dst carry cin,top∉i.wires) ∧
  (diagP xs dst carry cin).any (fun i => decide (label∈i.wires))=true ∧ label≠c

instance (xs dst carry : List Wire) (cin : Wire) : Decidable (CoreGeometry xs dst carry cin) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem not_wires_of_each (P : Program) (q : Wire) (h : ∀i∈P,q∉i.wires) : q∉wires P := by
  induction P with
  | nil => simp [wires]
  | cons i P ih =>
    simp only [wires,Finset.mem_union,not_or]
    exact ⟨h i List.mem_cons_self,ih (fun j hj => h j (List.mem_cons_of_mem _ hj))⟩

theorem mem_wires_of_any (P : Program) (q : Wire)
    (h : P.any (fun i => decide (q∈i.wires))=true) : q∈wires P := by
  induction P with
  | nil => simp at h
  | cons i P ih =>
    simp only [List.any_cons,Bool.or_eq_true,decide_eq_true_eq] at h
    simp only [wires,Finset.mem_union]
    rcases h with here | later
    · exact Or.inl here
    · exact Or.inr (ih later)

theorem geometry_of_core (xs dst carry : List Wire) (cin : Wire)
    (core : CoreGeometry xs dst carry cin) : Geometry xs dst carry cin := by
  obtain ⟨split,hn,ha,hct,hcp,htp,hlp,hg,hqc,htB,labelMem,labelNe⟩ := core
  exact ⟨split,hn,ha,hct,not_wires_of_each _ _ hcp,
    not_wires_of_each _ _ htp,not_wires_of_each _ _ hlp,hg,hqc,
    not_wires_of_each _ _ htB,mem_wires_of_any _ _ labelMem,labelNe⟩

theorem active_of_W_core (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (lo : CoreGeometry R.lo R.dlo R.carry R.cin)
    (hi : CoreGeometry R.hi R.dhi R.carry R.cin) : DI4Square.Active R :=
  active_of_W_geometry R w hn (geometry_of_core _ _ _ _ lo) (geometry_of_core _ _ _ _ hi)

end ECDSAAdd.Entrant.DI5DiagonalGeometry

namespace ECDSAAdd.Entrant.DI5PaddedGeometry
open ECDSAAdd Arithmetic DiagSq DI4PaddedHigh
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true

def Geometry (xs dst cs : List Wire) (ci : Wire) : Prop :=
  let n:=xs.length
  let c:=cs.getD (2*n-3) 0
  let d:=cs.getD (2*n-2) 0
  let z:=dst.getD (2*n-2) 0
  let top:=dst.getD (2*n-1) 0
  xs.length=33 ∧ dst.length=66 ∧ dst.Nodup ∧
  dAddZ xs dst cs ci=lead xs dst cs ci ++ heads xs dst cs ++ following xs dst cs ++ rest xs dst cs ci ∧
  [xs.getD (n-3) 0,xs.getD (n-2) 0,dst.getD (2*n-3) 0,z,top,cs.getD (2*n-4) 0,c,d].Nodup ∧
  c∉dst ∧ d∉dst ∧ z∈dst ∧ top∈dst ∧
  c∉wires (maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0)) ∧
  d∉wires (maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0)) ∧
  top∉wires (maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0)) ∧
  (∀a∈frames xs dst cs,a.Good) ∧
  (∀a∈frames xs dst cs,c≠a.c ∧ d≠a.c ∧ top≠a.c) ∧
  (∀i∈rest xs dst cs ci, ZeroReadDevelop.targetOf i≠z) ∧
  (∀i∈rest xs dst cs ci, ZeroReadDevelop.targetOf i≠top)

instance (xs dst cs : List Wire) (ci : Wire) : Decidable (Geometry xs dst cs ci) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Resource transport for the two-majority replacement; long context programs stay opaque. -/
theorem replace_head_resources (P Q : Program) (a b y z top ci c d : Wire)
    (hn : [a,b,y,z,top,ci,c,d].Nodup)
    (oldPhysical : GatePhysical (P ++ oldHead a b y z ci c d ++ Q)) :
    wires (P ++ newHead b z c ++ Q) ⊆ wires (P ++ oldHead a b y z ci c d ++ Q) ∧
    GatePhysical (P ++ newHead b z c ++ Q) ∧
    toffoliCount (P ++ newHead b z c ++ Q)+2 = toffoliCount (P ++ oldHead a b y z ci c d ++ Q) ∧
    measurementCount (P ++ newHead b z c ++ Q) = measurementCount (P ++ oldHead a b y z ci c d ++ Q) ∧
    Challenge.gateSlots (P ++ newHead b z c ++ Q) ≤ Challenge.gateSlots (P ++ oldHead a b y z ci c d ++ Q) := by
  have support : wires (newHead b z c) ⊆ wires (oldHead a b y z ci c d) := by
    intro q hq
    simp only [newHead,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    rcases hq with (rfl | rfl) | (rfl | rfl)
    all_goals simp [oldHead,mappedMajority,borrowMajority,majority,wires,Instr.wires]
  have ndB := (List.nodup_cons.mp hn).2
  have bAway := (List.nodup_cons.mp ndB).1
  have ndY := (List.nodup_cons.mp ndB).2
  have ndZ := (List.nodup_cons.mp ndY).2
  have zAway := (List.nodup_cons.mp ndZ).1
  have hbc : b≠c := fun he => bAway (by simp [he])
  have hzc : z≠c := fun he => zAway (by simp [he])
  have physical : GatePhysical (newHead b z c) := by
    simp [newHead,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,hbc,hzc]
  have oldT : toffoliCount (oldHead a b y z ci c d)=2 := rfl
  have newT : toffoliCount (newHead b z c)=0 := rfl
  have oldM : measurementCount (oldHead a b y z ci c d)=0 := rfl
  have newM : measurementCount (newHead b z c)=0 := rfl
  have oldS : Challenge.gateSlots (oldHead a b y z ci c d)=16 := rfl
  have newS : Challenge.gateSlots (newHead b z c)=2 := rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [wires_append]
    exact Finset.union_subset_union
      (Finset.union_subset_union (Finset.Subset.refl _) support) (Finset.Subset.refl _)
  · simp only [gatePhysical_append] at oldPhysical ⊢
    exact ⟨⟨oldPhysical.1.1,physical⟩,oldPhysical.2⟩
  · simp only [toffoliCount_append,oldT,newT]
    omega
  · simp only [measurementCount_append,oldM,newM]
  · simp only [Challenge.gateSlots_append,oldS,newS]
    omega

/-- The first 16 structural fields imply all five resource fields algebraically. -/
theorem shape_of_geometry (xs dst cs : List Wire) (ci : Wire)
    (geometry : Geometry xs dst cs ci) (oldPhysical : GatePhysical (dSubZ xs dst cs ci)) :
    DI4PaddedHigh.Shape xs dst cs ci := by
  obtain ⟨hx,hd,hdnd,split,nd,hcn,hdn,hzm,htm,hcp,hdp,htp,hg,hq,kz,kt⟩ := geometry
  let n := xs.length
  let P := notRegister dst ++ lead xs dst cs ci
  let Q := following xs dst cs ++ rest xs dst cs ci ++ notRegister dst
  have old : GatePhysical (P ++ oldHead (xs.getD (n-3) 0) (xs.getD (n-2) 0)
      (dst.getD (2*n-3) 0) (dst.getD (2*n-2) 0) (cs.getD (2*n-4) 0)
      (cs.getD (2*n-3) 0) (cs.getD (2*n-2) 0) ++ Q) := by
    simpa only [P,Q,n,dSubZ,split,heads,List.append_assoc] using oldPhysical
  have resources := replace_head_resources P Q (xs.getD (n-3) 0) (xs.getD (n-2) 0)
    (dst.getD (2*n-3) 0) (dst.getD (2*n-2) 0) (dst.getD (2*n-1) 0)
    (cs.getD (2*n-4) 0) (cs.getD (2*n-3) 0) (cs.getD (2*n-2) 0) nd old
  have result : wires (DI4PaddedHigh.program xs dst cs ci) ⊆ wires (dSubZ xs dst cs ci) ∧
      GatePhysical (DI4PaddedHigh.program xs dst cs ci) ∧
      toffoliCount (DI4PaddedHigh.program xs dst cs ci)+2=toffoliCount (dSubZ xs dst cs ci) ∧
      measurementCount (DI4PaddedHigh.program xs dst cs ci)=measurementCount (dSubZ xs dst cs ci) ∧
      Challenge.gateSlots (DI4PaddedHigh.program xs dst cs ci)≤Challenge.gateSlots (dSubZ xs dst cs ci) := by
    simpa only [P,Q,n,DI4PaddedHigh.program,DI4PaddedHigh.inner,dSubZ,split,heads,List.append_assoc] using resources
  exact ⟨hx,hd,hdnd,split,nd,hcn,hdn,hzm,htm,hcp,hdp,htp,hg,hq,kz,kt,
    result.1,result.2.1,result.2.2.1,result.2.2.2.1,result.2.2.2.2⟩

/-- Existing general square physicality supplies the old high-diagonal physicality. -/
theorem active_of_W_geometry (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (geometry : Geometry R.hi R.dhi R.carry R.cin) : DI4PadMake.Active R := by
  have old := DiagSq.makeZ_physical R w hn
  simp only [DiagSq.makeZ,headBlockZ,gatePhysical_append] at old
  exact shape_of_geometry _ _ _ _ geometry old.1.2.2

end ECDSAAdd.Entrant.DI5PaddedGeometry

namespace ECDSAAdd.Entrant.DI5PaddedGeometry
open ECDSAAdd Arithmetic DiagSq DI4PaddedHigh
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true

def CoreGeometry (xs dst cs : List Wire) (ci : Wire) : Prop :=
  let n:=xs.length
  let c:=cs.getD (2*n-3) 0
  let d:=cs.getD (2*n-2) 0
  let z:=dst.getD (2*n-2) 0
  let top:=dst.getD (2*n-1) 0
  dAddZ xs dst cs ci=lead xs dst cs ci ++ heads xs dst cs ++ following xs dst cs ++ rest xs dst cs ci ∧
  [xs.getD (n-3) 0,xs.getD (n-2) 0,dst.getD (2*n-3) 0,z,top,cs.getD (2*n-4) 0,c,d].Nodup ∧
  c∉dst ∧ d∉dst ∧ z∈dst ∧ top∈dst ∧
  c∉wires (maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0)) ∧
  d∉wires (maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0)) ∧
  top∉wires (maj0 (xs.getD 0 0) (dst.getD 0 0) ci (cs.getD 0 0)) ∧
  (∀a∈frames xs dst cs,a.Good) ∧
  (∀a∈frames xs dst cs,c≠a.c ∧ d≠a.c ∧ top≠a.c) ∧
  (∀i∈rest xs dst cs ci, ZeroReadDevelop.targetOf i≠z) ∧
  (∀i∈rest xs dst cs ci, ZeroReadDevelop.targetOf i≠top)

instance (xs dst cs : List Wire) (ci : Wire) : Decidable (CoreGeometry xs dst cs ci) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Dimensions and the quadratic destination-Nodup check come from existing W/count facts. -/
theorem geometry_of_W_core (R : KRegs) (w : R.W) (h33 : R.h=33) (h66 : R.bank.length=66)
    (hn : R.all.Nodup) (core : CoreGeometry R.hi R.dhi R.carry R.cin) :
    Geometry R.hi R.dhi R.carry R.cin := by
  have lengths := R.lens w
  have xsLen : R.hi.length=33 := by omega
  have dstLen : R.dhi.length=66 := by omega
  have dstNodup : R.dhi.Nodup := knd hn (fun q => by
    have counts := R.counts q
    simp only [KRegs.all,List.count_cons,List.count_append] at counts ⊢
    omega)
  exact ⟨xsLen,dstLen,dstNodup,core⟩

theorem active_of_W_core (R : KRegs) (w : R.W) (h33 : R.h=33) (h66 : R.bank.length=66)
    (hn : R.all.Nodup) (core : CoreGeometry R.hi R.dhi R.carry R.cin) : DI4PadMake.Active R :=
  active_of_W_geometry R w hn (geometry_of_W_core R w h33 h66 hn core)

end ECDSAAdd.Entrant.DI5PaddedGeometry

namespace ECDSAAdd.Entrant.DI4C7Fast
open ECDSAAdd Arithmetic DI4LastCarry
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- The structural/local geometry part of Shape. Its tail check inspects each
instruction separately and never constructs the whole suffix's wire Finset. -/
def CoreData (xs ys cs : List Wire) (ci label : Wire) : Prop :=
  let n := ys.length
  let c := cs.getD (n-2) 0
  let top := ys.getD (n-1) 0
  let x := xs.getD (n-1) 0
  let bit : MappedBit := ⟨some (xs.getD (n-2) 0),false⟩
  let y := ys.getD (n-2) 0
  let cin := cs.getD (n-3) 0
  old xs ys cs ci = pre xs ys cs ci ++ mappedMajority bit y cin c ++
    [.CX x top,.CX c top] ++ tail xs ys cs ci ∧
  [y,cin,c].Nodup ∧ (∀q∈bit.wire,q∉[y,cin,c]) ∧ top≠c ∧ x≠c ∧
  (∀a∈frames xs ys cs ci,a.Good) ∧
  (∀a∈frames xs ys cs ci,c≠a.c ∧ top≠a.c ∧ label≠a.c ∧ x≠a.c) ∧
  (∀i∈tail xs ys cs ci,top∉i.wires)

instance (xs ys cs : List Wire) (ci label : Wire) : Decidable (CoreData xs ys cs ci label) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Geometry (R : KRegs) : Prop :=
  CoreData (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (R.S.getD (R.S.length-1) 0)

instance (R : KRegs) : Decidable (Geometry R) :=
  inferInstanceAs (Decidable (CoreData _ _ _ _ _))

theorem not_wires_of_each (P : Program) (q : Wire) (h : ∀i∈P,q∉i.wires) : q∉wires P := by
  induction P with
  | nil => simp [wires]
  | cons i P ih =>
    simp only [wires,Finset.mem_union,not_or]
    exact ⟨h i List.mem_cons_self,ih (fun j hj => h j (List.mem_cons_of_mem _ hj))⟩

/-- Generic local-splice wire transport. Long surrounding programs are opaque. -/
theorem splice_wires (A B D : Program) (x top c label : Wire) :
    wires (A ++ [.CX label c,.CX top c] ++ [.CX x top,.CX c top] ++ D) ⊆
      insert label (wires (A ++ B ++ [.CX x top,.CX c top] ++ D)) := by
  intro q hq
  simp only [wires_append] at hq ⊢
  simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.notMem_empty,or_false] at hq ⊢
  tauto

theorem two_cx_tc (a b c d : Wire) : toffoliCount [.CX a b,.CX c d]=0 := rfl
theorem two_cx_mc (a b c d : Wire) : measurementCount [.CX a b,.CX c d]=0 := rfl
theorem two_cx_slots (a b c d : Wire) : Challenge.gateSlots [.CX a b,.CX c d]=2 := rfl

/-- All expensive resource fields follow from the existing physical program and
the local split; no large-program wire/properness/count decision is evaluated. -/
theorem shape_of_core (xs ys cs : List Wire) (ci label : Wire)
    (hc : CoreData xs ys cs ci label)
    (hp : GatePhysical (old xs ys cs ci))
    (hlc : label≠cs.getD (ys.length-2) 0) : Shape xs ys cs ci label := by
  obtain ⟨he,hn,ha,hct,hxc,hg,hq,hB⟩ := hc
  refine ⟨he,hn,ha,hct,hxc,hg,hq,not_wires_of_each _ _ hB,?_,?_,?_,?_,?_⟩
  · simpa only [program,he] using
      splice_wires (pre xs ys cs ci)
        (mappedMajority ⟨some (xs.getD (ys.length-2) 0),false⟩
          (ys.getD (ys.length-2) 0) (cs.getD (ys.length-3) 0) (cs.getD (ys.length-2) 0))
        (tail xs ys cs ci) (xs.getD (ys.length-1) 0) (ys.getD (ys.length-1) 0)
        (cs.getD (ys.length-2) 0) label
  · rw [he] at hp
    simp only [gatePhysical_append] at hp
    have hnew : GatePhysical [.CX label (cs.getD (ys.length-2) 0),
        .CX (ys.getD (ys.length-1) 0) (cs.getD (ys.length-2) 0)] := by
      intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · exact hlc
      · rcases List.mem_cons.mp hi with rfl|hi
        · exact hct
        · cases hi
    simp only [program,gatePhysical_append]
    exact ⟨⟨⟨hp.1.1.1,hnew⟩,hp.1.2⟩,hp.2⟩
  · have hb := (mappedBit_counts ⟨some (xs.getD (ys.length-2) 0),false⟩
        (ys.getD (ys.length-2) 0) (cs.getD (ys.length-3) 0) (cs.getD (ys.length-2) 0)).1
    simp only [program,he,toffoliCount_append,two_cx_tc,hb]
    omega
  · have hb := (mappedBit_counts ⟨some (xs.getD (ys.length-2) 0),false⟩
        (ys.getD (ys.length-2) 0) (cs.getD (ys.length-3) 0) (cs.getD (ys.length-2) 0)).2.1
    simp only [program,he,measurementCount_append,two_cx_mc,hb]
  · have hb : Challenge.gateSlots
        (mappedMajority ⟨some (xs.getD (ys.length-2) 0),false⟩
          (ys.getD (ys.length-2) 0) (cs.getD (ys.length-3) 0) (cs.getD (ys.length-2) 0))=6 := rfl
    simp only [program,he,Challenge.gateSlots_append,two_cx_slots,hb]
    omega

theorem label_ne_carry (R : KRegs) (w : R.W) (hn : R.all.Nodup) :
    R.S.getD (R.S.length-1) 0 ≠
      (R.carry.take (R.T.length-1)).getD (R.T.length-2) 0 := by
  have hs : 1≤R.S.length := by
    have := w.S;have := w.hh;have := w.h4;omega
  have hm := RawClearCarryIntegration.getD_mem R.S (R.S.length-1) (by omega)
  have hc := (DI4LastCarry.members R w).1
  have hd : ∀q∈R.S,q∉R.carry := kdis hn (fun q => by
    simp only [KRegs.all,List.count_cons,List.count_append]
    omega)
  intro he
  rw [←he] at hc
  exact hd _ hm hc

/-- First staging lemma: geometry contains only structural and per-instruction
checks; W/Nodup supply old physicality and the new label/target separation. -/
theorem active_of_geometry (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (geometry : Geometry R) : DI4LastCarry.Active R :=
  shape_of_core _ _ _ _ _ geometry (R.c7g_physical hn) (label_ne_carry R w hn)

end ECDSAAdd.Entrant.DI4C7Fast

namespace ECDSAAdd.Entrant.PDSplitLeafSquare
open Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
  StairSquareContract StairSquareAssembly StairSquareHolesCore StairSquareDirectFold
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Common wire definitions and allowed-site table -/

abbrev hs : List Wire := StairSqLoopA.hostDomain

/-- All non-hole, non-flag/swap wires in the concrete square layout and external pool. -/
def allowedWires : List Wire :=
  (K0.wires ++ E0 ++ [G0, D0]).filter (fun q => !hs.contains q && q != 4761 && q != 4834 && q != 4875)

theorem K0_eq : K0 = StairSquareBChecks.K4DQ.LBF := StairSquareBChecks.K4DQ.LB_eq

def E0F : List Wire := List.range' 5093 51 ++ List.range' 5399 246 ++ List.range' 5648 3

theorem E0_eq : E0 = E0F := by
  change (List.range' 978 51).map Baselines.layout.core.poolWire ++
      (List.range' 1284 246).map Baselines.layout.core.poolWire ++
      (List.range' 1533 3).map Baselines.layout.core.poolWire = E0F
  rw [StairSquareBChecks.K4DQ.blk 978 51 (by decide),
      StairSquareBChecks.K4DQ.blk 1284 246 (by decide),
      StairSquareBChecks.K4DQ.blk 1533 3 (by decide)]
  rfl

theorem G0_eq : G0 = 4113 := by decide +kernel
theorem D0_eq : D0 = 5655 := StairSquareBChecks.K4DQ.pw_lt 1540 (by decide)

private theorem holesA_lit : StairSqLoopA.holes = List.range' 4840 35 ++ List.range' 4876 4 := by
  rw [StairSqLoopA.holes, List.map_append, StairSquareBChecks.K4DQ.blk 725 35 (by decide),
      StairSquareBChecks.K4DQ.blk 761 4 (by decide)]

private theorem hs_lit : hs = (List.range' 4840 35 ++ List.range' 4876 4) ++ List.range' 4835 5 := by
  rw [hs, StairSqLoopA.hostDomain, holesA_lit, StairSquareBChecks.K4DQ.blk 720 5 (by decide)]

theorem allowedWires_eq :
    allowedWires = (StairSquareBChecks.K4DQ.LBF.wires ++ E0F ++ [4113, 5655]).filter
      (fun q => !((List.range' 4840 35 ++ List.range' 4876 4) ++ List.range' 4835 5).contains q &&
        q != 4761 && q != 4834 && q != 4875) := by
  rw [allowedWires, K0_eq, E0_eq, G0_eq, D0_eq, hs_lit]

private theorem sub_allowedWires (L : List Wire)
    (hIn : ∀ q ∈ L, q ∈ K0.wires ++ E0 ++ [G0, D0])
    (hOut : ∀ q ∈ L, q ∉ 4761 :: 4834 :: 4875 :: hs) :
    ∀ q ∈ L, q ∈ allowedWires := by
  intro q hq
  rw [allowedWires, List.mem_filter]
  refine ⟨hIn q hq, ?_⟩
  have ho := hOut q hq
  simp only [List.mem_cons, not_or] at ho
  simp [ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

private theorem not_mem_allowedWires_4834 : (4834 : Wire) ∉ allowedWires := by
  rw [allowedWires, List.mem_filter]; simp

private theorem not_mem_allowedWires_4875 : (4875 : Wire) ∉ allowedWires := by
  rw [allowedWires, List.mem_filter]; simp

private theorem hosts88_fast : LowAccCarryDevelop.hosts88 =
    FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
      (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4) := by
  rw [LowAccCarryDevelop.hosts88, LowAccCarryDevelop.loans88]
  change FullBTemp.hostR K0 :: FullBTemp.hostP K0 :: (FullBTemp.loans K0 ++ (accReg K0).take 4) = _
  rw [K0_eq]

private theorem hostsBSup_fast : ReorderedBSupportResearch.hosts =
    StairSquareBChecks.K4DQ.LBF.core.sumCarry ::
      (FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4)) := by
  rw [ReorderedBSupportResearch.hosts, hosts88_fast]
  change K0.core.sumCarry :: _ = _
  rw [K0_eq]

private theorem hostsB95_fast : B95Research.hosts =
    (StairSquareBChecks.K4DQ.LBF.core.sumCarry ::
      (FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4))) ++
      [4757, 4758, 4759, 4505, 4506, 4507] := by
  rw [B95Research.hosts, hostsBSup_fast]

private theorem keepKB_fast : B95Research.keepK =
    ((StairSquareBChecks.K4DQ.LBF.core.sumCarry ::
      (FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4))) ++
      [4757, 4758, 4759, 4505, 4506, 4507]).filter
      (fun q => !(((FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4)).take 44).contains q)) := by
  rw [B95Research.keepK, hostsB95_fast, hosts88_fast]

private theorem hsC_fast : C163Low4Middle.hs =
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4 := by
  change (K0.core.work.drop 165 ++ [D0]) ++ K0.core.work.take 4 = _
  rw [K0_eq, D0_eq]

private theorem hostsCFix_fast : ReorderedCFixed.hosts =
    StairSquareBChecks.K4DQ.LBF.core.work.getD 163 0 ::
    StairSquareBChecks.K4DQ.LBF.core.work.getD 164 0 ::
    StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 ::
    ((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4) := by
  rw [ReorderedCFixed.hosts, hsC_fast]
  change K0.core.work.getD 163 0 :: K0.core.work.getD 164 0 :: K0.core.product.getD 1 0 :: _ = _
  rw [K0_eq]

private theorem hostsC105_fast : C105Research.hosts =
    (StairSquareBChecks.K4DQ.LBF.core.work.getD 163 0 ::
     StairSquareBChecks.K4DQ.LBF.core.work.getD 164 0 ::
     StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 ::
     ((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4)) ++
      [4757, 4758, 4759, 4505, 4506, 4507] := by
  rw [C105Research.hosts, hostsCFix_fast]

private theorem keepKC_fast : C105Research.keepK =
    ((StairSquareBChecks.K4DQ.LBF.core.work.getD 163 0 ::
      StairSquareBChecks.K4DQ.LBF.core.work.getD 164 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 ::
      ((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4)) ++
      [4757, 4758, 4759, 4505, 4506, 4507]).filter
      (fun q => !((((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4).take 44).contains q)) := by
  rw [C105Research.keepK, hostsC105_fast, hsC_fast]

private def hsAF : List Wire :=
  ((((StairSquareBChecks.K4DQ.LBF.core.work.drop 163).take 33 ++ (StairSquareBChecks.K4DQ.LBF.core.work.drop 255).take 1 ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 227).take 28 ++ (StairSquareBChecks.K4DQ.LBF.core.work.drop 201).take 10 ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 212).take 15 ++ (StairSquareBChecks.K4DQ.LBF.core.work.drop 211).take 1 ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 196).take 5) ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 161).take 2) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4) ++ [5655]

private theorem hsA_fast : ReorderedAFixed.hs = hsAF := by
  rw [show ReorderedAFixed.hs = A161Low4Geometry.hs100 from rfl, A161Low4Geometry.hs100,
      A161Low4Geometry.hs99, A161Low4Geometry.loans93, hsAF]
  change ((((K0.core.work.drop 163).take 33 ++ (K0.core.work.drop 255).take 1 ++
      (K0.core.work.drop 227).take 28 ++ (K0.core.work.drop 201).take 10 ++
      (K0.core.work.drop 212).take 15 ++ (K0.core.work.drop 211).take 1 ++
      (K0.core.work.drop 196).take 5) ++
      (K0.core.work.drop 161).take 2) ++ K0.core.work.take 4) ++ [D0] = _
  rw [K0_eq, D0_eq]

private theorem hostsAFix_fast : ReorderedAFixed.hosts =
    StairSquareBChecks.K4DQ.LBF.core.sumCarry :: (StairSquareBChecks.K4DQ.LBF.core.product.drop 256).getD 1 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 :: hsAF := by
  rw [ReorderedAFixed.hosts, hsA_fast]
  change K0.core.sumCarry :: (K0.core.product.drop 256).getD 1 0 :: K0.core.product.getD 1 0 :: _ = _
  rw [K0_eq]

private theorem hostsA109_fast : A109Research.hosts =
    (StairSquareBChecks.K4DQ.LBF.core.sumCarry :: (StairSquareBChecks.K4DQ.LBF.core.product.drop 256).getD 1 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 :: hsAF) ++ [4757, 4758, 4759, 4505, 4506, 4507] := by
  rw [A109Research.hosts, hostsAFix_fast]

private theorem keepKA_fast : A109Research.keepK =
    ((StairSquareBChecks.K4DQ.LBF.core.sumCarry :: (StairSquareBChecks.K4DQ.LBF.core.product.drop 256).getD 1 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 :: hsAF) ++ [4757, 4758, 4759, 4505, 4506, 4507]).filter
      (fun q => !((hsAF.take 44).contains q)) := by
  rw [A109Research.keepK, hostsA109_fast, hsA_fast]

/-- Spilled T5 wires inside `K0.core.work` (evicted from carry caches during the body). -/
def workTA : List Wire :=
  (A109Research.keepK.filter (fun q => (K0.core.work.drop 163).contains q)).take 32

def workTB : List Wire :=
  (B95Research.keepK.filter (fun q => (K0.core.work.drop 207).contains q)) ++
  (K0.core.work.drop 196).take 2 ++ [D0]

def workTC : List Wire := (K0.core.work.drop 209).take 34

/-- Twenty-wire swap moving `work[196..197]` and `work[207..224]` off `StairSquareBEFoldK.efold` onto clean `work[225..255]` hosts. -/
def efSwapB : List (Wire × Wire) :=
  ((B95Research.keepK.filter (fun q => (K0.core.work.drop 207).contains q && !((K0.core.work.drop 225).contains q))) ++
    (K0.core.work.drop 196).take 2).zip
    ((LowAccCarryDevelop.hosts88.take 44).filter (fun q => (K0.core.work.drop 225).contains q))

theorem workTA_def :
    workTA = (A109Research.keepK.filter (fun q => (StairSquareBChecks.K4DQ.LBF.core.work.drop 163).contains q)).take 32 := by
  rw [workTA, K0_eq]

theorem workTB_def :
    workTB = (B95Research.keepK.filter (fun q => (StairSquareBChecks.K4DQ.LBF.core.work.drop 207).contains q)) ++
      (StairSquareBChecks.K4DQ.LBF.core.work.drop 196).take 2 ++ [5655] := by
  rw [workTB, K0_eq, D0_eq]

theorem workTC_def :
    workTC = (StairSquareBChecks.K4DQ.LBF.core.work.drop 209).take 34 := by
  rw [workTC, K0_eq]

theorem efSwapB_def :
    efSwapB = ((B95Research.keepK.filter (fun q =>
        (StairSquareBChecks.K4DQ.LBF.core.work.drop 207).contains q &&
        !((StairSquareBChecks.K4DQ.LBF.core.work.drop 225).contains q))) ++
      (StairSquareBChecks.K4DQ.LBF.core.work.drop 196).take 2).zip
      ((LowAccCarryDevelop.hosts88.take 44).filter (fun q => (StairSquareBChecks.K4DQ.LBF.core.work.drop 225).contains q)) := by
  rw [efSwapB, K0_eq]

private def workTAF : List Wire :=
  [4738, 4739, 4740, 4741, 4742, 4743, 4744, 4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752, 4753,
   4754, 4755, 4702, 4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710, 4711, 4713, 4714, 4715, 4716]

private def workTBF : List Wire :=
  [4747, 4748, 4749, 4750, 4751, 4752, 4753, 4754, 4755, 4708, 4709, 4710, 4711, 4712, 4714, 4715,
   4716, 4717, 4718, 4719, 4720, 4721, 4722, 4723, 4724, 4725, 4726, 4727, 4713, 4697, 4698, 5655]

private def workTCF : List Wire := List.range' 4710 34

private def efSwapBF : List (Wire × Wire) :=
  [(4708, 4756), (4709, 4728), (4710, 4729), (4711, 4730), (4712, 4731),
   (4714, 4732), (4715, 4733), (4716, 4734), (4717, 4735), (4718, 4736),
   (4719, 4737), (4720, 4738), (4721, 4739), (4722, 4740), (4723, 4741),
   (4724, 4742), (4725, 4743), (4713, 4744), (4697, 4745), (4698, 4746)]

theorem workTA_lit : workTA = workTAF := by rw [workTA_def, keepKA_fast]; decide +kernel
theorem workTB_lit : workTB = workTBF := by rw [workTB_def, keepKB_fast]; decide +kernel
theorem workTC_lit : workTC = workTCF := by rw [workTC_def]; decide +kernel
theorem efSwapB_lit : efSwapB = efSwapBF := by rw [efSwapB_def, keepKB_fast, hosts88_fast]; decide +kernel

theorem work_T_geometry :
    workTA.length = 32 ∧ workTA.Nodup ∧
    workTB.length = 32 ∧ workTB.Nodup ∧
    workTC.length = 34 ∧ workTC.Nodup ∧
    efSwapB.length = 20 ∧
    (holesOf efSwapB ++ hostsOf efSwapB).Nodup ∧
    (∀ q ∈ workTA, q ∈ A109Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
    (∀ q ∈ workTB.take 31, q ∈ B95Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
    (∀ q ∈ workTC, q ∈ C105Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
    (∀ q ∈ workTA, q ∈ allowedWires) ∧
    (∀ q ∈ workTB, q ∈ allowedWires) ∧
    (∀ q ∈ workTC, q ∈ allowedWires) ∧
    (∀ ab ∈ efSwapB, ab.1 ∈ workTB ∧ ab.2 ∈ K0.core.work.drop 207 ∧
      ab.2 ∈ LowAccCarryDevelop.hosts88.take 44 ∧ ab.2 ∉ workTB ∧ ab.2 ∈ allowedWires ∧ ab.2 ≠ K0.core.normFlag) ∧
    (∀ q ∈ workTB, q ∉ holesOf efSwapB → q ∉ StairSquareBEFold.carryB K0) := by
  have hAllowedAll : ∀ q ∈ workTA ++ workTB ++ workTC ++ hostsOf efSwapB, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, hs_lit]; decide +kernel))
  have hAllowedA : ∀ q ∈ workTA, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hAllowedB : ∀ q ∈ workTB, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hAllowedC : ∀ q ∈ workTC, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hAllowedEf : ∀ q ∈ hostsOf efSwapB, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hRest : workTA.length = 32 ∧ workTA.Nodup ∧
      workTB.length = 32 ∧ workTB.Nodup ∧
      workTC.length = 34 ∧ workTC.Nodup ∧
      efSwapB.length = 20 ∧
      (holesOf efSwapB ++ hostsOf efSwapB).Nodup ∧
      (∀ q ∈ workTA, q ∈ A109Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
      (∀ q ∈ workTB.take 31, q ∈ B95Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
      (∀ q ∈ workTC, q ∈ C105Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
      (∀ ab ∈ efSwapB, ab.1 ∈ workTB ∧ ab.2 ∈ K0.core.work.drop 207 ∧
        ab.2 ∈ LowAccCarryDevelop.hosts88.take 44 ∧ ab.2 ∉ workTB ∧ ab.2 ≠ K0.core.normFlag) ∧
      (∀ q ∈ workTB, q ∉ holesOf efSwapB → q ∉ StairSquareBEFold.carryB K0) := by
    rw [workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, keepKA_fast, keepKB_fast, keepKC_fast, hosts88_fast, K0_eq]; decide +kernel
  refine ⟨hRest.1, hRest.2.1, hRest.2.2.1, hRest.2.2.2.1, hRest.2.2.2.2.1, hRest.2.2.2.2.2.1,
    hRest.2.2.2.2.2.2.1, hRest.2.2.2.2.2.2.2.1, hRest.2.2.2.2.2.2.2.2.1, hRest.2.2.2.2.2.2.2.2.2.1,
    hRest.2.2.2.2.2.2.2.2.2.2.1, hAllowedA, hAllowedB, hAllowedC, ?_, hRest.2.2.2.2.2.2.2.2.2.2.2.2⟩
  intro ab hab
  have hr := hRest.2.2.2.2.2.2.2.2.2.2.2.1 ab hab
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hAllowedEf ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩), hr.2.2.2.2⟩

/-! ## Clean-sum diagonal leaf wrappers (`makeC` / `clearC`) -/

section CleanDiag
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical

theorem makeC_clean (Q : KRegs) (w : Q.W) (he : Q.bank.length = 2 * Q.h) (hh : Q.h = 32 ∨ Q.h = 33)
    (hn : Q.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue Q.dst s.basis = 0) (hS0 : regValue Q.S s.basis = 0)
    (hT0 : regValue Q.T s.basis = 0) (hz0 : regValue Q.z s.basis = 0)
    (hp0 : regValue Q.pad s.basis = 0) (hc0 : regValue Q.carry s.basis = 0)
    (hi0 : s.basis Q.cin = false) :
    (run (LowZero18Diagonal.makeC Q) m s).phase = s.phase ∧
    regValue Q.dst (run (LowZero18Diagonal.makeC Q) m s).basis = (regValue Q.bank s.basis) ^ 2 ∧
    regValue Q.T (run (LowZero18Diagonal.makeC Q) m s).basis = 2 * regValue Q.lo s.basis * regValue Q.hi s.basis ∧
    ∀ q, q ∉ Q.dst → q ∉ Q.T → (run (LowZero18Diagonal.makeC Q) m s).basis q = s.basis q := by
  have hX0 : regValue (Q.S ++ Q.T) s.basis = 0 := by rw [regValue_append, hS0, hT0]; simp
  have r := LowZero18Diagonal.diag_sq_cl_make Q w he hh hn Q.z (fun _ h => h) s m hd0 hX0 hp0 hc0 hz0 hi0
  refine ⟨r.1, r.2.1, ?_, ?_⟩
  · rw [r.2.2.1.2, Q.lo_mod w, Q.hi_div w]
  · intro q hd hT
    by_cases hS : q ∈ Q.S
    · exact ((regValue_zero Q.S _).mp r.2.2.1.1 q hS).trans ((regValue_zero Q.S _).mp hS0 q hS).symm
    · exact r.2.2.2 q hd (fun hx => (List.mem_append.mp hx).elim hS hT)

theorem clearC_clean (Q : KRegs) (w : Q.W) (he : Q.bank.length = 2 * Q.h) (hh : Q.h = 32 ∨ Q.h = 33)
    (hn : Q.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue Q.dst s.basis = (regValue Q.bank s.basis) ^ 2)
    (hS0 : regValue Q.S s.basis = 0)
    (hT0 : regValue Q.T s.basis = 2 * regValue Q.lo s.basis * regValue Q.hi s.basis)
    (hz0 : regValue Q.z s.basis = 0) (hp0 : regValue Q.pad s.basis = 0)
    (hc0 : regValue Q.carry s.basis = 0) (hi0 : s.basis Q.cin = false) :
    (run (DI4Square.clearC Q) m s).phase = s.phase ∧
    regValue Q.dst (run (DI4Square.clearC Q) m s).basis = 0 ∧
    regValue Q.T (run (DI4Square.clearC Q) m s).basis = 0 ∧
    ∀ q, q ∉ Q.dst → q ∉ Q.T → (run (DI4Square.clearC Q) m s).basis q = s.basis q := by
  have hI : Q.invC (regValue Q.bank s.basis) s.basis := by
    refine ⟨hS0, ?_⟩
    rw [hT0, Q.lo_mod w, Q.hi_div w]
  have r := DI4Square.diag_sq_cl_clear Q w he hh hn Q.z (fun _ h => h) s m hd0 hI hp0 hc0 hz0 hi0
  have hST := (regValue_append Q.S Q.T _).symm.trans r.2.2.1
  have hST0 := Nat.add_eq_zero_iff.mp hST
  have hS1 : regValue Q.S (run (DI4Square.clearC Q) m s).basis = 0 := hST0.1
  have hT1 : regValue Q.T (run (DI4Square.clearC Q) m s).basis = 0 :=
    (Nat.mul_eq_zero.mp hST0.2).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
  refine ⟨r.1, r.2.1, hT1, ?_⟩
  intro q hd hT
  by_cases hS : q ∈ Q.S
  · exact ((regValue_zero Q.S _).mp hS1 q hS).trans ((regValue_zero Q.S _).mp hS0 q hS).symm
  · exact r.2.2.2 q hd (fun hx => (List.mem_append.mp hx).elim hS hT)

theorem makeC_physical (Q : KRegs) (w : Q.W) (hn : Q.all.Nodup) :
    GatePhysical (LowZero18Diagonal.makeC Q) :=
  (gatePhysical_append _ _).mpr ⟨LowZero18Diagonal.make_physical Q w hn, Q.scl1591_physical w hn⟩

theorem clearC_physical (Q : KRegs) (w : Q.W) (hn : Q.all.Nodup) :
    GatePhysical (DI4Square.clearC Q) :=
  (gatePhysical_append _ _).mpr
    ⟨Q.smkT_physical w hn (Q.piece_physical hn).1,
      (DI4Square.clear_resources Q).2.1 (RawClearSquare.clear_physical Q w hn)⟩

theorem makeC_support (Q : KRegs) (w : Q.W) :
    wires (LowZero18Diagonal.makeC Q) ⊆ Q.all.toFinset := by
  rw [LowZero18Diagonal.makeC, wires_append]
  exact Finset.union_subset (LowZero18Diagonal.make_support Q w) (Q.scl1591_support w)

theorem clearC_support (Q : KRegs) (w : Q.W) :
    wires (DI4Square.clearC Q) ⊆ Q.all.toFinset := by
  rw [DI4Square.clearC, wires_append]
  exact Finset.union_subset (Q.smkT_support w (Q.piece_support w).1)
    (DI4Square.clear_support Q w)

theorem makeC_counts (Q : KRegs) (w : Q.W) (he : Q.bank.length = 2 * Q.h) :
    toffoliCount (LowZero18Diagonal.makeC Q) = DiagSq.cost Q - 11 - DiagSq.parR Q ∧
    measurementCount (LowZero18Diagonal.makeC Q) = DiagSq.cost Q - 4 - DiagSq.parR Q + (Q.bank.length - Q.h) := by
  have m := LowZero18Diagonal.make_counts Q w he
  have sc := Q.scl1591_counts w
  simp only [LowZero18Diagonal.makeC, toffoliCount_append, measurementCount_append]
  exact ⟨by omega, by omega⟩

theorem diag32_counts (Q : KRegs) (w : Q.W) (hh : Q.h = 32) (hb : Q.bank.length = 64) :
    toffoliCount (LowZero18Diagonal.makeC Q) = toffoliCount (LowZero18Diagonal.make Q) ∧
    measurementCount (LowZero18Diagonal.makeC Q) = measurementCount (LowZero18Diagonal.make Q) + 32 ∧
    toffoliCount (LowZero18Diagonal.clearC Q) = toffoliCount (LowZero18Diagonal.clear Q) + 31 ∧
    measurementCount (LowZero18Diagonal.clearC Q) = measurementCount (LowZero18Diagonal.clear Q) + 32 := by
  have sc := Q.scl1591_counts w
  have sm := Q.smkT_counts w
  have pc := Q.piece_counts w
  simp only [LowZero18Diagonal.makeC, LowZero18Diagonal.clearC, LowZero18Diagonal.clear, RawClearSquare.clearC,
    toffoliCount_append, measurementCount_append]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem diag33_counts (Q : KRegs) (w : Q.W) (hh : Q.h = 33) (hb : Q.bank.length = 66) :
    toffoliCount (LowZero18Diagonal.makeC Q) = toffoliCount (LowZero18Diagonal.make Q) ∧
    measurementCount (LowZero18Diagonal.makeC Q) = measurementCount (LowZero18Diagonal.make Q) + 33 ∧
    toffoliCount (LowZero18Diagonal.clearC Q) = toffoliCount (LowZero18Diagonal.clear Q) + 32 ∧
    measurementCount (LowZero18Diagonal.clearC Q) = measurementCount (LowZero18Diagonal.clear Q) + 33 := by
  have sc := Q.scl1591_counts w
  have sm := Q.smkT_counts w
  have pc := Q.piece_counts w
  simp only [LowZero18Diagonal.makeC, LowZero18Diagonal.clearC, LowZero18Diagonal.clear, RawClearSquare.clearC,
    toffoliCount_append, measurementCount_append]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem diag33_exact (Q : KRegs) (w : Q.W) (hh : Q.h = 33) (hb : Q.bank.length = 66) :
    toffoliCount (LowZero18Diagonal.makeC Q) + toffoliCount (LowZero18Diagonal.clearC Q) = 3881 ∧
    measurementCount (LowZero18Diagonal.makeC Q) + measurementCount (LowZero18Diagonal.clearC Q) = 4152 := by
  have he : Q.bank.length = 2 * Q.h := by omega
  have ⟨mt, mm⟩ := LowZero18Diagonal.make_counts Q w he
  have ⟨ct, cm⟩ := RawClearSquare.clear_counts Q w he
  have ⟨d1, d2, d3, d4⟩ := diag33_counts Q w hh hb
  have hc : DiagSq.cost Q = 2048 := by simp only [DiagSq.cost, hb, hh]; decide +kernel
  have hlo : Q.lo.length = 33 := by simp [KRegs.lo, hb, hh]
  have hhi : Q.hi.length = 33 := by simp [KRegs.hi, hb, hh]
  have hS : Q.S.length = 34 := by have := w.S; omega
  have hp : DiagSq.parR Q = 2 := by simp only [DiagSq.parR, hlo, hhi, hS]; decide +kernel
  rw [hc, hp] at mt mm
  rw [hc, hh] at ct
  rw [hc] at cm
  change toffoliCount (LowZero18Diagonal.clearC Q) = toffoliCount (RawClearSquare.clear Q) + 32 at d3
  change measurementCount (LowZero18Diagonal.clearC Q) = measurementCount (RawClearSquare.clear Q) + 33 at d4
  exact ⟨by omega, by omega⟩

theorem tsq65_exact (xs dst pad carry : List Wire) (cin : Wire)
    (hx : xs.length = 65) (hd : dst.length = 130) (hp : 1 ≤ pad.length) (hc : 129 ≤ carry.length) :
    toffoliCount (TrimMid.tsqM xs dst pad carry cin) +
      toffoliCount (PlainKnownClear.program xs dst pad carry cin) = 4286 ∧
    measurementCount (TrimMid.tsqM xs dst pad carry cin) +
      measurementCount (PlainKnownClear.program xs dst pad carry cin) = 4413 := by
  have q := TrimSquare3.tsq3_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have qm := TrimMid.tsqM_counts_rel xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have q4 := TrimSquare4.tsqcM4_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have qn := PlainKnownClear.program_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have hk : signedSquareRowsCount 65 + 130 - 3 = 2207 := by decide +kernel
  rw [hx, hd] at q
  rw [hx, TrimMid.par_65] at qm qn
  exact ⟨by omega, by omega⟩

end CleanDiag
end ECDSAAdd.Entrant.PDSplitLeafSquare
namespace ECDSAAdd.Entrant.DI4Leaves
open ECDSAAdd Arithmetic DiagSq KRegs
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical

def make (Q : KRegs) (p : Prop) [Decidable p] : Program :=
  if p then DI4PadMake.makeC Q else LowZero18Diagonal.makeC Q

def clear (Q : KRegs) (p : Prop) [Decidable p] : Program :=
  if p then DI4PadClear.clearC Q else DI4Square.clearC Q

theorem make_clean (Q : KRegs) (p : Prop) [Decidable p] (w : Q.W) (he : Q.bank.length = 2 * Q.h) (hh : Q.h = 32 ∨ Q.h = 33)
    (hn : Q.all.Nodup) (s : State) (m : List Bool)
    (hpad : p → Q.h=33 ∧ Q.bank.length=66) (hbank : p → regValue Q.bank s.basis<2^65)
    (hd0 : regValue Q.dst s.basis = 0) (hS0 : regValue Q.S s.basis = 0)
    (hT0 : regValue Q.T s.basis = 0) (hz0 : regValue Q.z s.basis = 0)
    (hp0 : regValue Q.pad s.basis = 0) (hc0 : regValue Q.carry s.basis = 0)
    (hi0 : s.basis Q.cin = false) :
    (run (make Q p) m s).phase = s.phase ∧
    regValue Q.dst (run (make Q p) m s).basis = (regValue Q.bank s.basis) ^ 2 ∧
    regValue Q.T (run (make Q p) m s).basis = 2 * regValue Q.lo s.basis * regValue Q.hi s.basis ∧
    ∀ q, q ∉ Q.dst → q ∉ Q.T → (run (make Q p) m s).basis q = s.basis q := by
  by_cases hp : p
  · rw [make,if_pos hp]
    exact DI4PadMake.makeC_clean Q w he (hpad hp).1 (hpad hp).2 hn s m hd0 hS0 hT0 hz0 hp0 hc0 hi0 (hbank hp)
  · rw [make,if_neg hp]
    exact PDSplitLeafSquare.makeC_clean Q w he hh hn s m hd0 hS0 hT0 hz0 hp0 hc0 hi0

theorem clear_clean (Q : KRegs) (p : Prop) [Decidable p] (w : Q.W) (he : Q.bank.length = 2 * Q.h) (hh : Q.h = 32 ∨ Q.h = 33)
    (hn : Q.all.Nodup) (s : State) (m : List Bool)
    (hpad : p → Q.h=33 ∧ Q.bank.length=66) (hbank : p → regValue Q.bank s.basis<2^65)
    (hd0 : regValue Q.dst s.basis = (regValue Q.bank s.basis) ^ 2)
    (hS0 : regValue Q.S s.basis = 0)
    (hT0 : regValue Q.T s.basis = 2 * regValue Q.lo s.basis * regValue Q.hi s.basis)
    (hz0 : regValue Q.z s.basis = 0) (hp0 : regValue Q.pad s.basis = 0)
    (hc0 : regValue Q.carry s.basis = 0) (hi0 : s.basis Q.cin = false) :
    (run (clear Q p) m s).phase = s.phase ∧
    regValue Q.dst (run (clear Q p) m s).basis = 0 ∧
    regValue Q.T (run (clear Q p) m s).basis = 0 ∧
    ∀ q, q ∉ Q.dst → q ∉ Q.T → (run (clear Q p) m s).basis q = s.basis q := by
  by_cases hp : p
  · rw [clear,if_pos hp]
    exact DI4PadClear.clearC_clean Q w he (hpad hp).1 (hpad hp).2 hn s m hd0 hS0 hT0 hz0 hp0 hc0 hi0 (hbank hp)
  · rw [clear,if_neg hp]
    exact PDSplitLeafSquare.clearC_clean Q w he hh hn s m hd0 hS0 hT0 hz0 hp0 hc0 hi0

theorem make_support (Q : KRegs) (p : Prop) [Decidable p] (w : Q.W) :
    wires (make Q p)⊆Q.all.toFinset := by
  by_cases hp : p
  · rw [make,if_pos hp]
    exact (DI4PadMake.makeC_support Q w).trans (PDSplitLeafSquare.makeC_support Q w)
  · rw [make,if_neg hp]
    exact PDSplitLeafSquare.makeC_support Q w

theorem make_physical (Q : KRegs) (p : Prop) [Decidable p] (w : Q.W) (hn : Q.all.Nodup) :
    GatePhysical (make Q p) := by
  by_cases hp : p
  · rw [make,if_pos hp]
    exact DI4PadMake.makeC_physical Q w hn
  · rw [make,if_neg hp]
    exact PDSplitLeafSquare.makeC_physical Q w hn

theorem make_measurements (Q : KRegs) (p : Prop) [Decidable p] (w : Q.W) :
    measurementCount (make Q p)=measurementCount (LowZero18Diagonal.makeC Q) := by
  by_cases hp : p
  · rw [make,if_pos hp]
    exact DI4PadMake.makeC_measurements Q w
  · rw [make,if_neg hp]

theorem make_slots (Q : KRegs) (p : Prop) [Decidable p] (w : Q.W) :
    Challenge.gateSlots (make Q p)≤Challenge.gateSlots (LowZero18Diagonal.makeC Q) := by
  by_cases hp : p
  · rw [make,if_pos hp]
    exact DI4PadMake.makeC_slots Q w
  · rw [make,if_neg hp]

theorem clear_support (Q : KRegs) (p : Prop) [Decidable p] (w : Q.W) :
    wires (clear Q p)⊆Q.all.toFinset := by
  by_cases hp : p
  · rw [clear,if_pos hp]
    exact DI4PadClear.clearC_support Q w
  · rw [clear,if_neg hp]
    exact PDSplitLeafSquare.clearC_support Q w

theorem clear_physical (Q : KRegs) (p : Prop) [Decidable p] (w : Q.W) (hn : Q.all.Nodup) :
    GatePhysical (clear Q p) := by
  by_cases hp : p
  · rw [clear,if_pos hp]
    exact DI4PadClear.clearC_physical Q w hn
  · rw [clear,if_neg hp]
    exact PDSplitLeafSquare.clearC_physical Q w hn

theorem clear_measurements (Q : KRegs) (p : Prop) [Decidable p] (_w : Q.W) :
    measurementCount (clear Q p)=measurementCount (LowZero18Diagonal.clearC Q) := by
  by_cases hp : p
  · rw [clear,if_pos hp]
    exact DI4PadClear.clearC_measurements Q
  · rw [clear,if_neg hp]
    exact DI4Square.clearC_measurements Q

theorem clear_slots (Q : KRegs) (p : Prop) [Decidable p] (_w : Q.W) :
    Challenge.gateSlots (clear Q p)≤Challenge.gateSlots (LowZero18Diagonal.clearC Q) := by
  by_cases hp : p
  · rw [clear,if_pos hp]
    exact DI4PadClear.clearC_slots Q
  · rw [clear,if_neg hp]
    exact DI4Square.clearC_slots Q

end ECDSAAdd.Entrant.DI4Leaves

namespace ECDSAAdd.Entrant.PDSplitLeafSquare
open Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout StairSquareContract StairSquareAssembly StairSquareHolesCore StairSquareDirectFold
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


/-! ## Split-65 Karatsuba core (`R` + `R8` + three clean-sum diagonal leaves) -/

/-- Configuration of one 128- or 129-bit split Karatsuba leaf with `R8.z` reusing `R.S.take 62`. -/
structure SplitCfg where
  n : Nat
  src : List Wire
  dst : List Wire
  workT : List Wire
  zReal4 : List Wire
  zpad : Wire
  zdst0 : Wire
  zdst1 : Wire
  carry : List Wire
  T1 : List Wire
  T2 : List Wire
  T5 : List Wire

namespace SplitCfg
variable (c : SplitCfg)

def bank : List Wire := K0.inputBank.take c.n
def S : List Wire := ((LowZero18LowK.ktmp K0).take 66).take (c.n - 63)
def T : List Wire := (E0.take 132).take (2 * (c.n - 63))

def R : KRegs :=
  { h := 64, bank := c.bank, dst := c.dst, S := c.S, T := c.T,
    z := c.zReal4 ++ List.range' 20000 58, pad := K0.leafPad, carry := c.carry, cin := K0.core.cin }

def R8 : KRegs :=
  { h := 64, bank := c.bank, dst := c.dst, S := List.range' 20100 (c.n - 63), T := c.T,
    z := c.S.take 62, pad := K0.leafPad, carry := c.carry, cin := K0.core.cin }

def qCarry : List Wire := c.carry.take 100
def qZ30 : List Wire := (c.carry.drop 100).take 30
def qZ31 : List Wire := (c.carry.drop 100).take 31
def qS33 : List Wire := (c.carry.drop 131).take 33
def qS34 : List Wire := (c.carry.drop 131).take 34

def Q1 : KRegs :=
  { h := 32, bank := c.R.lo, dst := c.R.dlo, S := c.qS33, T := c.T1,
    z := c.qZ30, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }

def Q2 : KRegs :=
  if c.n = 128 then
    { h := 32, bank := c.R.hi, dst := c.R.dhi, S := c.qS33, T := c.T2,
      z := c.qZ30, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }
  else
    { h := 33, bank := c.R.hi ++ [c.zpad], dst := c.R.dhi ++ [c.zdst0, c.zdst1], S := c.qS34, T := c.T2,
      z := c.qZ31, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }

def Q5 : KRegs :=
  if c.n = 128 then
    { h := 33, bank := c.S ++ [c.zpad], dst := c.T ++ [c.zdst0, c.zdst1], S := c.qS34, T := c.T5,
      z := c.qZ31, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }
  else
    { h := 33, bank := c.S, dst := c.T, S := c.qS34, T := c.T5,
      z := c.qZ31, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }

/-- Wires that remain non-zero between `make` and `clear` (in addition to `dst`). -/
def liveT : List Wire := c.T ++ c.T1 ++ c.T2 ++ c.T5

/-- All real wires (all `< 20000`) used by `make` and `clear`. -/
def realAll : List Wire :=
  K0.core.cin :: c.bank ++ c.dst ++ c.S ++ c.T ++ c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++
    K0.leafPad ++ c.carry ++ c.T1 ++ c.T2 ++ c.T5

/-- All scratch wires that must start zero and return to zero after `make`. -/
def cleanScratch : List Wire :=
  c.S ++ c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++ K0.leafPad ++ c.carry

def makeRef : Program :=
  LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5 ++ c.R.m6h ++ c.R.m7k ++ c.R.scl1591 ++ c.R8.m8z

def make : Program :=
  LowZero18Diagonal.makeC c.Q1 ++ DI4Leaves.make c.Q2 (c.n=129) ++ c.R.smk ++
    DI4Leaves.make c.Q5 (c.n=128) ++ c.R.m6h ++ c.R.m7k ++ c.R.scl1591 ++ c.R8.m8z

def clearRef : Program :=
  c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    LowZero18Diagonal.clearC c.Q5 ++ c.R.scl1591 ++
    LowZero18Diagonal.clearC c.Q2 ++ LowZero18Diagonal.clearC c.Q1

def clear : Program :=
  DI4Merge.safe c.R8 ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    DI4Leaves.clear c.Q5 (c.n=128) ++ c.R.scl1591 ++
    DI4Leaves.clear c.Q2 (c.n=129) ++ DI4Square.clearC c.Q1

end SplitCfg

/-! ### Concrete configurations for Branches A, B, and C -/

private def cleanRem (n : Nat) (wT : List Wire) : List Wire :=
  (K0.leafCarry.filter (fun q => !wT.contains q)) ++
  (if n = 128 then [(LowZero18LowK.ktmp K0).getD 65 0] else []) ++
  [(LowZero18LowK.ktmp K0).getD 66 0] ++
  ((LowZero18LowK.ktmp K0).drop 113).take 10

def cfgA : SplitCfg :=
  let rem := cleanRem 128 workTA
  { n := 128, src := K0.core.low, dst := K0.core.product.take 256, workT := workTA,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0.drop 132).take 66, T2 := (E0.drop 232).take 66,
    T5 := [E0.getD 231 0] ++ (E0.drop 198).take 33 ++ workTA ++ [E0.getD 298 0, E0.getD 299 0] }

def cfgB : SplitCfg :=
  let rem := cleanRem 128 workTB
  { n := 128, src := K0.core.high, dst := K0.core.product.take 256, workT := workTB,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0.drop 132).take 66, T2 := (E0.drop 232).take 66,
    T5 := [E0.getD 231 0] ++ (E0.drop 198).take 33 ++ workTB ++ [E0.getD 298 0, E0.getD 299 0] }

def cfgC : SplitCfg :=
  let rem := cleanRem 129 workTC
  { n := 129, src := K0.core.sum, dst := K0.core.product, workT := workTC,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0.drop 132).take 66, T2 := (E0.drop 232).take 68,
    T5 := (E0.drop 198).take 34 ++ workTC }

/-! ### Fast `K4DQ.LBF` / `E0F` / literal mirrors for kernel evaluation -/

private def cleanRemF (n : Nat) (wT : List Wire) : List Wire :=
  (StairSquareBChecks.K4DQ.LBF.leafCarry.filter (fun q => !wT.contains q)) ++
  (if n = 128 then [(LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).getD 65 0] else []) ++
  [(LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).getD 66 0] ++
  ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).drop 113).take 10

private def cfgAF : SplitCfg :=
  let rem := cleanRemF 128 workTAF
  { n := 128, src := StairSquareBChecks.K4DQ.LBF.core.low, dst := StairSquareBChecks.K4DQ.LBF.core.product.take 256, workT := workTAF,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0F.drop 132).take 66, T2 := (E0F.drop 232).take 66,
    T5 := [E0F.getD 231 0] ++ (E0F.drop 198).take 33 ++ workTAF ++ [E0F.getD 298 0, E0F.getD 299 0] }

private def cfgBF : SplitCfg :=
  let rem := cleanRemF 128 workTBF
  { n := 128, src := StairSquareBChecks.K4DQ.LBF.core.high, dst := StairSquareBChecks.K4DQ.LBF.core.product.take 256, workT := workTBF,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0F.drop 132).take 66, T2 := (E0F.drop 232).take 66,
    T5 := [E0F.getD 231 0] ++ (E0F.drop 198).take 33 ++ workTBF ++ [E0F.getD 298 0, E0F.getD 299 0] }

private def cfgCF : SplitCfg :=
  let rem := cleanRemF 129 workTCF
  { n := 129, src := StairSquareBChecks.K4DQ.LBF.core.sum, dst := StairSquareBChecks.K4DQ.LBF.core.product, workT := workTCF,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0F.drop 132).take 66, T2 := (E0F.drop 232).take 68,
    T5 := (E0F.drop 198).take 34 ++ workTCF }

private theorem cfgA_fast : cfgA = cfgAF := by rw [cfgA, cfgAF, cleanRem, cleanRemF, workTA_lit, K0_eq, E0_eq]
private theorem cfgB_fast : cfgB = cfgBF := by rw [cfgB, cfgBF, cleanRem, cleanRemF, workTB_lit, K0_eq, E0_eq]
private theorem cfgC_fast : cfgC = cfgCF := by rw [cfgC, cfgCF, cleanRem, cleanRemF, workTC_lit, K0_eq, E0_eq]

private theorem SplitCfg.bank_fast (c : SplitCfg) :
    c.bank = StairSquareBChecks.K4DQ.LBF.inputBank.take c.n := by rw [SplitCfg.bank, K0_eq]
private theorem SplitCfg.S_fast (c : SplitCfg) :
    c.S = ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) := by rw [SplitCfg.S, K0_eq]
private theorem SplitCfg.T_fast (c : SplitCfg) :
    c.T = (E0F.take 132).take (2 * (c.n - 63)) := by rw [SplitCfg.T, E0_eq]
private theorem SplitCfg.liveT_fast (c : SplitCfg) :
    c.liveT = (E0F.take 132).take (2 * (c.n - 63)) ++ c.T1 ++ c.T2 ++ c.T5 := by
  rw [SplitCfg.liveT, SplitCfg.T_fast]
private theorem SplitCfg.realAll_fast (c : SplitCfg) :
    c.realAll = StairSquareBChecks.K4DQ.LBF.core.cin :: StairSquareBChecks.K4DQ.LBF.inputBank.take c.n ++
      c.dst ++ ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) ++
      (E0F.take 132).take (2 * (c.n - 63)) ++ c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++
      StairSquareBChecks.K4DQ.LBF.leafPad ++ c.carry ++ c.T1 ++ c.T2 ++ c.T5 := by
  rw [SplitCfg.realAll, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]
private theorem SplitCfg.cleanScratch_fast (c : SplitCfg) :
    c.cleanScratch = ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) ++
      c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++ StairSquareBChecks.K4DQ.LBF.leafPad ++ c.carry := by
  rw [SplitCfg.cleanScratch, SplitCfg.S_fast, K0_eq]
private def SplitCfg.RF (c : SplitCfg) : KRegs :=
  { h := 64, bank := StairSquareBChecks.K4DQ.LBF.inputBank.take c.n, dst := c.dst,
    S := ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63),
    T := (E0F.take 132).take (2 * (c.n - 63)), z := c.zReal4 ++ List.range' 20000 58,
    pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.carry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.R8F (c : SplitCfg) : KRegs :=
  { h := 64, bank := StairSquareBChecks.K4DQ.LBF.inputBank.take c.n, dst := c.dst,
    S := List.range' 20100 (c.n - 63), T := (E0F.take 132).take (2 * (c.n - 63)),
    z := (((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63)).take 62,
    pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.carry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.Q1F (c : SplitCfg) : KRegs :=
  { h := 32, bank := c.RF.lo, dst := c.RF.dlo, S := c.qS33, T := c.T1, z := c.qZ30,
    pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.Q2F (c : SplitCfg) : KRegs :=
  if c.n = 128 then
    { h := 32, bank := c.RF.hi, dst := c.RF.dhi, S := c.qS33, T := c.T2, z := c.qZ30,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }
  else
    { h := 33, bank := c.RF.hi ++ [c.zpad], dst := c.RF.dhi ++ [c.zdst0, c.zdst1],
      S := c.qS34, T := c.T2, z := c.qZ31,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.Q5F (c : SplitCfg) : KRegs :=
  if c.n = 128 then
    { h := 33, bank := ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) ++ [c.zpad],
      dst := (E0F.take 132).take (2 * (c.n - 63)) ++ [c.zdst0, c.zdst1],
      S := c.qS34, T := c.T5, z := c.qZ31,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }
  else
    { h := 33, bank := ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63),
      dst := (E0F.take 132).take (2 * (c.n - 63)),
      S := c.qS34, T := c.T5, z := c.qZ31,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private theorem SplitCfg.R_fast (c : SplitCfg) : c.R = c.RF := by
  rw [SplitCfg.R, SplitCfg.RF, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]
private theorem SplitCfg.R8_fast (c : SplitCfg) : c.R8 = c.R8F := by
  rw [SplitCfg.R8, SplitCfg.R8F, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]
private theorem SplitCfg.Q1_fast (c : SplitCfg) : c.Q1 = c.Q1F := by
  rw [SplitCfg.Q1, SplitCfg.Q1F, SplitCfg.R_fast, K0_eq]
private theorem SplitCfg.Q2_fast (c : SplitCfg) : c.Q2 = c.Q2F := by
  rw [SplitCfg.Q2, SplitCfg.Q2F, SplitCfg.R_fast, K0_eq]
private theorem SplitCfg.Q5_fast (c : SplitCfg) : c.Q5 = c.Q5F := by
  rw [SplitCfg.Q5, SplitCfg.Q5F, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]

/-- Valid geometry bundle for a concrete `SplitCfg`. -/
structure CfgValid (c : SplitCfg) : Prop where
  hn : c.n = 128 ∨ c.n = 129
  realNd : c.realAll.Nodup
  realLt : ∀ q ∈ c.realAll, q < 20000
  realAllowed : ∀ q ∈ c.realAll, q ∈ allowedWires
  bankLen : c.bank.length = c.n
  dstLen : c.dst.length = 2 * c.n
  sLen : c.S.length = c.n - 63
  tLen : c.T.length = 2 * (c.n - 63)
  z4Len : c.zReal4.length = 4
  carryLen : c.carry.length = 193
  padLen : K0.leafPad.length = 1
  t1Len : c.T1.length = 66
  t2Len : c.T2.length = if c.n = 128 then 66 else 68
  t5Len : c.T5.length = 68

private theorem memory_cfgA_valid_hnd : cfgA.realAll.Nodup :=
  PeakNodup.nodup_of_mask _ (by simp only [SplitCfg.realAll_fast, cfgA_fast]; decide +kernel)

private theorem memory_cfgA_valid_hlt : ∀ q ∈ cfgA.realAll, q < 20000 := fun q hq =>
  of_decide_eq_true (List.all_eq_true.mp (by simp only [SplitCfg.realAll_fast, cfgA_fast]; decide +kernel :
    cfgA.realAll.all (fun x => decide (x < 20000)) = true) q hq)

private theorem memory_cfgA_valid_hall : ∀ q ∈ cfgA.realAll, q ∈ allowedWires :=
  sub_allowedWires _
    (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgA_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
    (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgA_fast, hs_lit]; decide +kernel))

theorem cfgA_valid : CfgValid cfgA := by
  have hnd := memory_cfgA_valid_hnd
  have hlt := memory_cfgA_valid_hlt
  have hall := memory_cfgA_valid_hall
  refine ⟨Or.inl rfl, hnd, hlt, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cfgA_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq, E0_eq]; decide +kernel)

/-! Independent finite receipts bound replay reduction caches per geometry part. -/
private theorem memory_cfgB_valid_hnd : cfgB.realAll.Nodup :=
  PeakNodup.nodup_of_mask _ (by simp only [SplitCfg.realAll_fast, cfgB_fast]; decide +kernel)

private theorem memory_cfgB_valid_hlt : ∀ q ∈ cfgB.realAll, q < 20000 := fun q hq =>
  of_decide_eq_true (List.all_eq_true.mp (by simp only [SplitCfg.realAll_fast, cfgB_fast]; decide +kernel :
    cfgB.realAll.all (fun x => decide (x < 20000)) = true) q hq)

private theorem memory_cfgB_valid_hall : ∀ q ∈ cfgB.realAll, q ∈ allowedWires :=
  sub_allowedWires _
    (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgB_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
    (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgB_fast, hs_lit]; decide +kernel))

theorem cfgB_valid : CfgValid cfgB := by
  have hnd := memory_cfgB_valid_hnd
  have hlt := memory_cfgB_valid_hlt
  have hall := memory_cfgB_valid_hall
  refine ⟨Or.inl rfl, hnd, hlt, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cfgB_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq, E0_eq]; decide +kernel)

/-! Independent finite receipts bound replay reduction caches per geometry part. -/
private theorem memory_cfgC_valid_hnd : cfgC.realAll.Nodup :=
  PeakNodup.nodup_of_mask _ (by simp only [SplitCfg.realAll_fast, cfgC_fast]; decide +kernel)

private theorem memory_cfgC_valid_hlt : ∀ q ∈ cfgC.realAll, q < 20000 := fun q hq =>
  of_decide_eq_true (List.all_eq_true.mp (by simp only [SplitCfg.realAll_fast, cfgC_fast]; decide +kernel :
    cfgC.realAll.all (fun x => decide (x < 20000)) = true) q hq)

private theorem memory_cfgC_valid_hall : ∀ q ∈ cfgC.realAll, q ∈ allowedWires :=
  sub_allowedWires _
    (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgC_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
    (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgC_fast, hs_lit]; decide +kernel))

theorem cfgC_valid : CfgValid cfgC := by
  have hnd := memory_cfgC_valid_hnd
  have hlt := memory_cfgC_valid_hlt
  have hall := memory_cfgC_valid_hall
  refine ⟨Or.inr rfl, hnd, hlt, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq, E0_eq]; decide +kernel)

/-! ### Generic support, physicality, correctness, and counts for any valid `SplitCfg` -/

section SplitCore
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical

private def zeroHigh (s : State) : State :=
  { phase := s.phase, basis := fun q => if 20000 ≤ q then false else s.basis q }

private theorem run_below20000 (P : Program) (hsub : ∀ q ∈ wires P, q < 20000) (s : State) (m : List Bool) :
    (run P m s).phase = (run P m (zeroHigh s)).phase ∧
    ∀ q, q < 20000 → (run P m s).basis q = (run P m (zeroHigh s)).basis q := by
  have loc := ECDSAAdd.run_measured_locality P (wires P) (Finset.Subset.refl _) s (zeroHigh s) m rfl
    (fun q hq => by simp [zeroHigh, Nat.not_le.mpr (hsub q hq)])
  exact ⟨loc.1, fun q hq => by
    by_cases hw : q ∈ wires P
    · exact loc.2 q hw
    · rw [run_preserves_outside P m s q hw, run_preserves_outside P m (zeroHigh s) q hw]
      simp [zeroHigh, Nat.not_le.mpr hq]⟩

private theorem run_ge20000 (P : Program) (hsub : ∀ q ∈ wires P, q < 20000) (s : State) (m : List Bool)
    (q : Wire) (hq : 20000 ≤ q) : (run P m s).basis q = s.basis q :=
  run_preserves_outside P m s q (fun hw => absurd (hsub q hw) (Nat.not_lt.mpr hq))

private theorem list_nodup_of_count_le {A B : List Wire} (hB : B.Nodup) (h : ∀ q, A.count q ≤ B.count q) : A.Nodup :=
  List.nodup_iff_count_le_one.mpr (fun q => (h q).trans (List.nodup_iff_count_le_one.mp hB q))

theorem cfg_R_W (c : SplitCfg) (v : CfgValid c) : c.R.W := by
  rcases v.hn with hn | hn <;>
    exact ⟨by simp [SplitCfg.R], by simp [SplitCfg.R, v.bankLen, hn], by simp [SplitCfg.R, v.bankLen, hn],
      by simp [SplitCfg.R, v.dstLen, v.bankLen], by simp [SplitCfg.R, v.sLen, v.bankLen, hn],
      by simp [SplitCfg.R, v.tLen, v.sLen], by simp [SplitCfg.R, v.z4Len],
      by simp [SplitCfg.R, v.padLen], by simp [SplitCfg.R, v.bankLen, v.carryLen, hn]⟩

theorem cfg_R8_W (c : SplitCfg) (v : CfgValid c) : c.R8.W := by
  rcases v.hn with hn | hn <;>
    exact ⟨by simp [SplitCfg.R8], by simp [SplitCfg.R8, v.bankLen, hn], by simp [SplitCfg.R8, v.bankLen, hn],
      by simp [SplitCfg.R8, v.dstLen, v.bankLen], by simp [SplitCfg.R8, v.bankLen, hn],
      by simp [SplitCfg.R8, v.tLen, hn], by simp [SplitCfg.R8, v.sLen, hn],
      by simp [SplitCfg.R8, v.padLen], by simp [SplitCfg.R8, v.bankLen, v.carryLen, hn]⟩

theorem cfg_Q1_W (c : SplitCfg) (v : CfgValid c) : c.Q1.W ∧ c.Q1.bank.length = 2 * c.Q1.h := by
  have hlo : c.R.lo.length = 64 := by simp [KRegs.lo, SplitCfg.R, v.bankLen]; rcases v.hn with h | h <;> omega
  have hdlo : c.R.dlo.length = 128 := by simp [KRegs.dlo, SplitCfg.R, v.dstLen]; rcases v.hn with h | h <;> omega
  refine ⟨⟨by simp [SplitCfg.Q1], by simp [SplitCfg.Q1, hlo], by simp [SplitCfg.Q1, hlo],
    by simp [SplitCfg.Q1, hdlo, hlo], by simp [SplitCfg.Q1, SplitCfg.qS33, v.carryLen, hlo],
    by simp [SplitCfg.Q1, SplitCfg.qS33, v.carryLen, v.t1Len],
    by simp [SplitCfg.Q1, SplitCfg.qZ30, v.carryLen], by simp [SplitCfg.Q1, v.padLen],
    by simp [SplitCfg.Q1, SplitCfg.qCarry, v.carryLen, hlo]⟩, by simp [SplitCfg.Q1, hlo]⟩

theorem cfg_Q2_W (c : SplitCfg) (v : CfgValid c) :
    c.Q2.W ∧ c.Q2.bank.length = 2 * c.Q2.h ∧ (c.Q2.h = 32 ∨ c.Q2.h = 33) := by
  rcases v.hn with hn | hn
  · have hhi : c.R.hi.length = 64 := by simp [KRegs.hi, SplitCfg.R, v.bankLen, hn]
    have hdhi : c.R.dhi.length = 128 := by simp [KRegs.dhi, SplitCfg.R, v.dstLen, hn]
    have ht2 : c.T2.length = 66 := by simpa [hn] using v.t2Len
    refine ⟨⟨by simp [SplitCfg.Q2, hn], by simp [SplitCfg.Q2, hn, hhi], by simp [SplitCfg.Q2, hn, hhi],
      by simp [SplitCfg.Q2, hn, hdhi, hhi], by simp [SplitCfg.Q2, hn, SplitCfg.qS33, v.carryLen, hhi],
      by simp [SplitCfg.Q2, hn, SplitCfg.qS33, v.carryLen, ht2],
      by simp [SplitCfg.Q2, hn, SplitCfg.qZ30, v.carryLen], by simp [SplitCfg.Q2, hn, v.padLen],
      by simp [SplitCfg.Q2, hn, SplitCfg.qCarry, v.carryLen, hhi]⟩,
      by simp [SplitCfg.Q2, hn, hhi], Or.inl (by simp [SplitCfg.Q2, hn])⟩
  · have hne : c.n ≠ 128 := by omega
    have hhi : c.R.hi.length = 65 := by simp [KRegs.hi, SplitCfg.R, v.bankLen, hn]
    have hdhi : c.R.dhi.length = 130 := by simp [KRegs.dhi, SplitCfg.R, v.dstLen, hn]
    have ht2 : c.T2.length = 68 := by simpa [hne] using v.t2Len
    refine ⟨⟨by simp [SplitCfg.Q2, hne], by simp [SplitCfg.Q2, hne, hhi], by simp [SplitCfg.Q2, hne, hhi],
      by simp [SplitCfg.Q2, hne, hdhi, hhi], by simp [SplitCfg.Q2, hne, SplitCfg.qS34, v.carryLen, hhi],
      by simp [SplitCfg.Q2, hne, SplitCfg.qS34, v.carryLen, ht2],
      by simp [SplitCfg.Q2, hne, SplitCfg.qZ31, v.carryLen], by simp [SplitCfg.Q2, hne, v.padLen],
      by simp [SplitCfg.Q2, hne, SplitCfg.qCarry, v.carryLen, hhi]⟩,
      by simp [SplitCfg.Q2, hne, hhi], Or.inr (by simp [SplitCfg.Q2, hne])⟩

theorem cfg_Q5_W (c : SplitCfg) (v : CfgValid c) :
    c.Q5.W ∧ c.Q5.bank.length = 2 * c.Q5.h ∧ c.Q5.h = 33 := by
  rcases v.hn with hn | hn
  · have hS : c.S.length = 65 := by rw [v.sLen, hn]
    have hT : c.T.length = 130 := by rw [v.tLen, hn]
    refine ⟨⟨by simp [SplitCfg.Q5, hn], by simp [SplitCfg.Q5, hn, hS], by simp [SplitCfg.Q5, hn, hS],
      by simp [SplitCfg.Q5, hn, hT, hS], by simp [SplitCfg.Q5, hn, SplitCfg.qS34, v.carryLen, hS],
      by simp [SplitCfg.Q5, hn, SplitCfg.qS34, v.carryLen, v.t5Len],
      by simp [SplitCfg.Q5, hn, SplitCfg.qZ31, v.carryLen], by simp [SplitCfg.Q5, hn, v.padLen],
      by simp [SplitCfg.Q5, hn, SplitCfg.qCarry, v.carryLen, hS]⟩,
      by simp [SplitCfg.Q5, hn, hS], by simp [SplitCfg.Q5, hn]⟩
  · have hne : c.n ≠ 128 := by omega
    have hS : c.S.length = 66 := by rw [v.sLen, hn]
    have hT : c.T.length = 132 := by rw [v.tLen, hn]
    refine ⟨⟨by simp [SplitCfg.Q5, hne], by simp [SplitCfg.Q5, hne, hS], by simp [SplitCfg.Q5, hne, hS],
      by simp [SplitCfg.Q5, hne, hT, hS], by simp [SplitCfg.Q5, hne, SplitCfg.qS34, v.carryLen, hS],
      by simp [SplitCfg.Q5, hne, SplitCfg.qS34, v.carryLen, v.t5Len],
      by simp [SplitCfg.Q5, hne, SplitCfg.qZ31, v.carryLen], by simp [SplitCfg.Q5, hne, v.padLen],
      by simp [SplitCfg.Q5, hne, SplitCfg.qCarry, v.carryLen, hS]⟩,
      by simp [SplitCfg.Q5, hne, hS], by simp [SplitCfg.Q5, hne]⟩

private theorem count_take_drop_split3 (l : List Wire) (q : Wire) :
    (l.take 100).count q + ((l.drop 100).take 31).count q + ((l.drop 131).take 34).count q ≤ l.count q := by
  have s1 := congrArg (List.count q) (List.take_append_drop 100 l)
  have s2 := congrArg (List.count q) (List.take_append_drop 31 (l.drop 100))
  have d3 : (l.drop 100).drop 31 = l.drop 131 := by simp [List.drop_drop]
  rw [d3] at s2
  have s3 := (List.take_sublist 34 (l.drop 131)).count_le q
  simp only [List.count_append] at s1 s2
  omega

theorem cfg_nodups (c : SplitCfg) (v : CfgValid c) :
    c.R.all.Nodup ∧ c.R8.all.Nodup ∧ c.Q1.all.Nodup ∧ c.Q2.all.Nodup ∧ c.Q5.all.Nodup := by
  have hr := v.realNd
  have count_q (q : Wire) :
      c.qCarry.count q + c.qZ30.count q + c.qS33.count q ≤ c.carry.count q ∧
      c.qCarry.count q + c.qZ31.count q + c.qS34.count q ≤ c.carry.count q := by
    have h : c.qCarry.count q + c.qZ31.count q + c.qS34.count q ≤ c.carry.count q :=
      count_take_drop_split3 c.carry q
    have h30 : c.qZ30.count q ≤ c.qZ31.count q := by
      have : c.qZ30 = c.qZ31.take 30 := by simp [SplitCfg.qZ30, SplitCfg.qZ31, List.take_take]
      rw [this]; exact (List.take_sublist 30 _).count_le q
    have h33 : c.qS33.count q ≤ c.qS34.count q := by
      have : c.qS33 = c.qS34.take 33 := by simp [SplitCfg.qS33, SplitCfg.qS34, List.take_take]
      rw [this]; exact (List.take_sublist 33 _).count_le q
    exact ⟨by omega, h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply List.nodup_iff_count_le_one.mpr; intro q
    by_cases hq : q < 20000
    · have hr0 : (List.range' 20000 58).count q = 0 :=
        List.count_eq_zero.mpr (fun h => Nat.not_le.mpr hq (List.mem_range'_1.mp h).1)
      have hc := List.nodup_iff_count_le_one.mp hr q
      simp only [KRegs.all, SplitCfg.R, SplitCfg.realAll, List.count_cons, List.count_append, hr0] at hc ⊢; omega
    · have hreal0 : c.realAll.count q = 0 := List.count_eq_zero.mpr (fun h => hq (v.realLt q h))
      have hr1 := List.nodup_iff_count_le_one.mp (List.nodup_range' (s := 20000) (n := 58)) q
      simp only [KRegs.all, SplitCfg.R, SplitCfg.realAll, List.count_cons, List.count_append] at hreal0 ⊢; omega
  · apply List.nodup_iff_count_le_one.mpr; intro q
    by_cases hq : q < 20000
    · have hr0 : (List.range' 20100 (c.n - 63)).count q = 0 :=
        List.count_eq_zero.mpr (fun h => Nat.not_le.mpr (Nat.lt_trans hq (by decide : 20000 < 20100)) (List.mem_range'_1.mp h).1)
      have hc := List.nodup_iff_count_le_one.mp hr q
      have ht := (List.take_sublist 62 c.S).count_le q
      simp only [KRegs.all, SplitCfg.R8, SplitCfg.realAll, List.count_cons, List.count_append, hr0] at hc ⊢; omega
    · have hreal0 : c.realAll.count q = 0 := List.count_eq_zero.mpr (fun h => hq (v.realLt q h))
      have hr1 := List.nodup_iff_count_le_one.mp (List.nodup_range' (s := 20100) (n := c.n - 63)) q
      have ht := (List.take_sublist 62 c.S).count_le q
      simp only [KRegs.all, SplitCfg.R8, SplitCfg.realAll, List.count_cons, List.count_append] at hreal0 ⊢; omega
  · apply list_nodup_of_count_le hr; intro q
    have h1 := (List.take_sublist 64 c.bank).count_le q
    have h2 := (List.take_sublist (2 * 64) c.dst).count_le q
    have h3 := (count_q q).1
    simp only [KRegs.all, SplitCfg.Q1, SplitCfg.R, KRegs.lo, KRegs.dlo, SplitCfg.realAll,
      List.count_cons, List.count_append]; omega
  · apply list_nodup_of_count_le hr; intro q
    have h1 := (List.drop_sublist 64 c.bank).count_le q
    have h2 := (List.drop_sublist (2 * 64) c.dst).count_le q
    have h3 := count_q q
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_true, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.realAll,
        List.count_cons, List.count_append]; omega
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_false, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.realAll,
        List.count_cons, List.count_append, List.count_nil]; omega
  · apply list_nodup_of_count_le hr; intro q
    have h3 := (count_q q).2
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_true, SplitCfg.realAll,
        List.count_cons, List.count_append, List.count_nil]; omega
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_false, SplitCfg.realAll,
        List.count_cons, List.count_append]; omega

theorem q2_pad_dims (c : SplitCfg) (v : CfgValid c) (hp : c.n=129) :
    c.Q2.h=33 ∧ c.Q2.bank.length=66 := by
  have hn : c.n≠128 := by omega
  have hh : c.Q2.h=33 := by simp [SplitCfg.Q2,hn]
  exact ⟨hh,by rw [(cfg_Q2_W c v).2.1,hh]⟩

theorem q5_pad_dims (c : SplitCfg) (v : CfgValid c) (_hp : c.n=128) :
    c.Q5.h=33 ∧ c.Q5.bank.length=66 := by
  have hh := (cfg_Q5_W c v).2.2
  exact ⟨hh,by rw [(cfg_Q5_W c v).2.1,hh]⟩

theorem cfg_physical (c : SplitCfg) (v : CfgValid c) :
    GatePhysical c.make ∧ GatePhysical c.clear := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := (cfg_Q1_W c v).1; have w2 := (cfg_Q2_W c v).1; have w5 := (cfg_Q5_W c v).1
  obtain ⟨nR, nR8, n1, n2, n5⟩ := cfg_nodups c v
  have pR := c.R.piece_physical nR
  have p6 : GatePhysical c.R.m6h := c.R.m6h_physical wR nR (by
    have h := pR.2.2.1; simp only [gatePhysical_append] at h; exact h.1.1)
  have pc6 : GatePhysical c.R.c6h := c.R.c6h_physical wR nR (by
    have h := pR.2.2.2.1; simp only [gatePhysical_append] at h; exact h.2)
  refine ⟨?_, ?_⟩
  · simp only [SplitCfg.make, gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨⟨makeC_physical c.Q1 w1 n1, DI4Leaves.make_physical c.Q2 (c.n=129) w2 n2⟩, pR.1⟩,
      DI4Leaves.make_physical c.Q5 (c.n=128) w5 n5⟩, p6⟩, c.R.m7k_physical wR nR⟩, c.R.scl1591_physical wR nR⟩,
      c.R8.m8z_physical nR8⟩
  · simp only [SplitCfg.clear, gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨⟨(DI4Merge.safe_resources c.R8).2.1 (c.R8.c8g_physical nR8), c.R.smkT_physical wR nR pR.1⟩,
      c.R.c7t_physical nR⟩, pc6⟩, DI4Leaves.clear_physical c.Q5 (c.n=128) w5 n5⟩,
      c.R.scl1591_physical wR nR⟩, DI4Leaves.clear_physical c.Q2 (c.n=129) w2 n2⟩, clearC_physical c.Q1 w1 n1⟩

private theorem take_z_in_z4 (c : SplitCfg) (v : CfgValid c) (k : Nat) (hk : k ≤ 4) :
    ∀ q ∈ c.R.z.take k, q ∈ c.zReal4 := by
  intro q hq
  have e : c.R.z.take k = c.zReal4.take k := by
    rw [SplitCfg.R, List.take_append_of_le_length (by rw [v.z4Len]; omega)]
  rw [e] at hq
  exact List.mem_of_mem_take hq

theorem cfg_support (c : SplitCfg) (v : CfgValid c) :
    wires c.make ⊆ c.realAll.toFinset ∧ wires c.clear ⊆ c.realAll.toFinset := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := (cfg_Q1_W c v).1; have w2 := (cfg_Q2_W c v).1; have w5 := (cfg_Q5_W c v).1
  have mCin : K0.core.cin ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mBank {q} (h : q ∈ c.bank) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mDst {q} (h : q ∈ c.dst) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mS {q} (h : q ∈ c.S) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT {q} (h : q ∈ c.T) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mZ4 {q} (h : q ∈ c.zReal4) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mZpad : c.zpad ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mZdst0 : c.zdst0 ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mZdst1 : c.zdst1 ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mPad {q} (h : q ∈ K0.leafPad) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mCarry {q} (h : q ∈ c.carry) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT1 {q} (h : q ∈ c.T1) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT2 {q} (h : q ∈ c.T2) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT5 {q} (h : q ∈ c.T5) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have sQ1 : c.Q1.all.toFinset ⊆ c.realAll.toFinset := by
    intro q hq
    simp only [KRegs.all, SplitCfg.Q1, SplitCfg.R, KRegs.lo, KRegs.dlo, SplitCfg.qCarry, SplitCfg.qZ30,
      SplitCfg.qS33, List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h | h | h | h
    · exact mCin
    · exact mBank (List.mem_of_mem_take h)
    · exact mDst (List.mem_of_mem_take h)
    · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
    · exact mT1 h
    · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
    · exact mPad h
    · exact mCarry (List.mem_of_mem_take h)
  have sQ2 : c.Q2.all.toFinset ⊆ c.realAll.toFinset := by
    intro q hq
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_true, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.qCarry,
        SplitCfg.qZ30, SplitCfg.qS33, List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
      rcases hq with rfl | h | h | h | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mDst (List.mem_of_mem_drop h)
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT2 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_false, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.qCarry,
        SplitCfg.qZ31, SplitCfg.qS34, List.mem_toFinset, List.mem_cons, List.mem_append, List.mem_singleton,
        List.mem_nil_iff, or_false, or_assoc] at hq
      rcases hq with rfl | h | rfl | h | rfl | rfl | h | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mZpad
      · exact mDst (List.mem_of_mem_drop h)
      · exact mZdst0
      · exact mZdst1
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT2 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
  have sQ5 : c.Q5.all.toFinset ⊆ c.realAll.toFinset := by
    intro q hq
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_true, SplitCfg.qCarry, SplitCfg.qZ31, SplitCfg.qS34,
        List.mem_toFinset, List.mem_cons, List.mem_append, List.mem_singleton,
        List.mem_nil_iff, or_false, or_assoc] at hq
      rcases hq with rfl | h | rfl | h | rfl | rfl | h | h | h | h | h
      · exact mCin
      · exact mS h
      · exact mZpad
      · exact mT h
      · exact mZdst0
      · exact mZdst1
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT5 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_false, SplitCfg.qCarry, SplitCfg.qZ31, SplitCfg.qS34,
        List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
      rcases hq with rfl | h | h | h | h | h | h | h
      · exact mCin
      · exact mS h
      · exact mT h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT5 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
  obtain ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10⟩ := c.R.lens wR
  have sSmk : wires c.R.smk ⊆ c.realAll.toFinset := by
    have w3 := copyRegister_wires_subset none c.R.lo (c.R.S.take c.R.h)
    have w4 := addInPlace_wires (c.R.hi ++ c.R.zS) c.R.S (c.R.carry.take (c.R.S.length - 1)) c.R.cin
      (by simp [L1, L5, wR.S]) (by simp [SplitCfg.R, v.carryLen, v.sLen]; rcases v.hn with hn | hn <;> omega)
    intro q hq
    simp only [KRegs.smk, KRegs.m3, KRegs.m4, wires_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · have h := w3 hq
      simp only [Option.toList_none, List.nil_append, List.mem_toFinset, List.mem_append] at h
      rcases h with h | h
      · exact mBank (List.mem_of_mem_take h)
      · exact mS (List.mem_of_mem_take h)
    · rw [w4] at hq
      simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
      rcases hq with rfl | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mZ4 (take_z_in_z4 c v 1 (by decide) q h)
      · exact mS h
      · exact mCarry (List.mem_of_mem_take h)
  have sSmkT : wires c.R.smkT ⊆ c.realAll.toFinset := by
    intro q hq
    rcases Finset.mem_union.mp (c.R.smkT_wires hq) with h | h
    · exact sSmk h
    · rw [Finset.mem_singleton.mp h]
      exact mT (DiagSq.getD_in c.T 1 (by have := v.tLen; rcases v.hn with hn | hn <;> omega))
  have sScl : wires c.R.scl1591 ⊆ c.realAll.toFinset := by
    have a := FrontierSumCleanup1591Primitive.sub_support (c.R.hi ++ c.R.zS) c.R.S c.R.sumExpected1591
      (c.R.carry.take (c.R.S.length - 1)) c.R.cin
    have p := copyRegister_wires_subset none c.R.lo (c.R.S.take c.R.h)
    intro q hq
    simp only [KRegs.scl1591, wires_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · have h := a hq
      simp only [KRegs.sumExpected1591, KRegs.lo, KRegs.hi, KRegs.zS, List.mem_toFinset,
        List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mZ4 (take_z_in_z4 c v 1 (by decide) q h)
      · exact mS h
      · exact mBank (List.mem_of_mem_take h)
      · exact mZ4 (take_z_in_z4 c v (c.R.S.length - c.R.lo.length)
          (by rw [L0, wR.S]; rcases v.hn with hn | hn <;> simp [SplitCfg.R, v.bankLen, hn]) q h)
      · exact mCarry (List.mem_of_mem_take h)
    · have h := p hq
      simp only [Option.toList_none, List.nil_append, List.mem_toFinset, List.mem_append] at h
      rcases h with h | h
      · exact mBank (List.mem_of_mem_take h)
      · exact mS (List.mem_of_mem_take h)
  have hL6 : (c.R.dlo ++ c.R.zA).length = c.R.T.length := by
    rw [List.length_append, L2, L6]; simp [SplitCfg.R, v.tLen]; rcases v.hn with hn | hn <;> omega
  have hC6 : (c.R.carry.take (c.R.T.length - 1)).length + 1 = c.R.T.length := by
    simp [SplitCfg.R, v.carryLen, v.tLen]; rcases v.hn with hn | hn <;> omega
  have sM6 : wires c.R.m6 ⊆ c.realAll.toFinset := by
    have w6 := subInPlace_wires (c.R.dlo ++ c.R.zA) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL6 hC6
    intro q hq; rw [KRegs.m6, w6] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_take h)
    · exact mZ4 (take_z_in_z4 c v (c.R.T.length - 2 * c.R.h) (by simp [SplitCfg.R, v.tLen]; rcases v.hn with hn | hn <;> omega) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  have sC6 : wires c.R.c6 ⊆ c.realAll.toFinset := by
    have w6 := addInPlace_wires (c.R.dlo ++ c.R.zA) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL6 hC6
    intro q hq; rw [KRegs.c6, w6] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_take h)
    · exact mZ4 (take_z_in_z4 c v (c.R.T.length - 2 * c.R.h) (by simp [SplitCfg.R, v.tLen]; rcases v.hn with hn | hn <;> omega) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  have hL7 : (c.R.dhi ++ c.R.zB).length = c.R.T.length := by
    rw [List.length_append, L3, L7]; simp [SplitCfg.R, v.bankLen, v.tLen]; rcases v.hn with hn | hn <;> omega
  have sM7 : wires c.R.m7 ⊆ c.realAll.toFinset := by
    have w7 := subInPlace_wires (c.R.dhi ++ c.R.zB) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL7 hC6
    intro q hq; rw [KRegs.m7, w7] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_drop h)
    · exact mZ4 (take_z_in_z4 c v 2 (by decide) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  have sC7 : wires c.R.c7 ⊆ c.realAll.toFinset := by
    have w7 := addInPlace_wires (c.R.dhi ++ c.R.zB) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL7 hC6
    intro q hq; rw [KRegs.c7, w7] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_drop h)
    · exact mZ4 (take_z_in_z4 c v 2 (by decide) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  obtain ⟨_, _, _, _, M4, _, _, _, _, _, _⟩ := c.R8.lens wR8
  have hL8 : (c.R8.T ++ c.R8.zM).length = c.R8.dmid.length := by
    rw [List.length_append, KRegs.zM, List.length_take, M4]; simp [SplitCfg.R8, v.tLen, v.sLen, v.bankLen]; rcases v.hn with hn | hn <;> omega
  have hC8 : (c.R8.carry.take (c.R8.dmid.length - 1)).length + 1 = c.R8.dmid.length := by
    rw [List.length_take, M4]; simp [SplitCfg.R8, v.carryLen, v.bankLen]; rcases v.hn with hn | hn <;> omega
  have sM8 : wires c.R8.m8 ⊆ c.realAll.toFinset := by
    have w8 := addInPlace_wires (c.R8.T ++ c.R8.zM) c.R8.dmid (c.R8.carry.take (c.R8.dmid.length - 1)) c.R8.cin hL8 hC8
    intro q hq; rw [KRegs.m8, w8] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mT h
    · exact mS (List.mem_of_mem_take (List.mem_of_mem_take h))
    · exact mDst (List.mem_of_mem_drop h)
    · exact mCarry (List.mem_of_mem_take h)
  have sC8 : wires c.R8.c8 ⊆ c.realAll.toFinset := by
    have w8 := subInPlace_wires (c.R8.T ++ c.R8.zM) c.R8.dmid (c.R8.carry.take (c.R8.dmid.length - 1)) c.R8.cin hL8 hC8
    intro q hq; rw [KRegs.c8, w8] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mT h
    · exact mS (List.mem_of_mem_take (List.mem_of_mem_take h))
    · exact mDst (List.mem_of_mem_drop h)
    · exact mCarry (List.mem_of_mem_take h)
  refine ⟨?_, ?_⟩
  · simp only [SplitCfg.make, wires_append, Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨(makeC_support c.Q1 w1).trans sQ1, (DI4Leaves.make_support c.Q2 (c.n=129) w2).trans sQ2⟩, sSmk⟩,
      (DI4Leaves.make_support c.Q5 (c.n=128) w5).trans sQ5⟩, (c.R.m6h_wires_smk wR).trans (Finset.union_subset sM6 sSmk)⟩,
      (c.R.m7k_wires wR).trans sM7⟩, sScl⟩, (c.R8.m8z_wires wR8).trans sM8⟩
  · simp only [SplitCfg.clear, wires_append, Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨(DI4Merge.safe_resources c.R8).1.trans (Finset.union_subset (c.R8.c8g_wires.trans sC8) (by intro q hq; exact mBank (List.mem_toFinset.mp hq))), sSmkT⟩, c.R.c7t_wires.trans sC7⟩,
      (c.R.c6h_wires wR).trans sC6⟩, (DI4Leaves.clear_support c.Q5 (c.n=128) w5).trans sQ5⟩, sScl⟩,
      (DI4Leaves.clear_support c.Q2 (c.n=129) w2).trans sQ2⟩, (clearC_support c.Q1 w1).trans sQ1⟩

private theorem regValue_snoc_zero (r : List Wire) (z : Wire) (b : BasisState) (hz : b z = false) :
    regValue (r ++ [z]) b = regValue r b := by
  simp [regValue_append, regValue, hz]

private theorem regValue_snoc2_lt (r : List Wire) (z0 z1 : Wire) (b : BasisState)
    (hlt : regValue (r ++ [z0, z1]) b < 2 ^ r.length) :
    b z0 = false ∧ b z1 = false ∧ regValue r b = regValue (r ++ [z0, z1]) b := by
  have h := regValue_append r [z0, z1] b
  rw [h] at hlt
  have h01 : regValue [z0, z1] b = 0 := by
    by_contra hne
    have hpos : 1 ≤ regValue [z0, z1] b := Nat.one_le_iff_ne_zero.mpr hne
    have : 2 ^ r.length ≤ 2 ^ r.length * regValue [z0, z1] b := Nat.le_mul_of_pos_right _ hpos
    omega
  have hb0 : b z0 = false := (regValue_zero [z0, z1] b).mp h01 z0 (by simp)
  have hb1 : b z1 = false := (regValue_zero [z0, z1] b).mp h01 z1 (by simp)
  exact ⟨hb0, hb1, by rw [h, h01]; simp⟩

private theorem dmid_val (c : SplitCfg) (v : CfgValid c) (b : BasisState) :
    regValue c.R8.dmid b = regValue c.R8.dlo b / 2 ^ 64 + 2 ^ 64 * regValue c.R8.dhi b := by
  have hd : 128 ≤ c.dst.length := by rw [v.dstLen]; rcases v.hn with h | h <;> omega
  have h1 : c.R8.dmid = (c.dst.take 128).drop 64 ++ c.dst.drop 128 := by
    have e := congrArg (List.drop 64) (List.take_append_drop 128 c.dst)
    rw [List.drop_append_of_le_length (by simp [hd])] at e
    exact e.symm
  have hlen : ((c.dst.take 128).drop 64).length = 64 := by simp [hd]
  have hdiv : regValue ((c.dst.take 128).drop 64) b = regValue (c.dst.take 128) b / 2 ^ 64 := by
    have ea := regValue_append ((c.dst.take 128).take 64) ((c.dst.take 128).drop 64) b
    rw [List.take_append_drop] at ea
    have hl64 : ((c.dst.take 128).take 64).length = 64 := by simp [hd]
    have hlt := regValue_lt ((c.dst.take 128).take 64) b
    rw [hl64] at ea hlt
    rw [ea, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [h1, regValue_append, hlen, hdiv]; rfl

private theorem realAll_count (c : SplitCfg) (x : Wire) :
    c.realAll.count x =
      [K0.core.cin].count x + c.bank.count x + c.dst.count x + c.S.count x + c.T.count x +
      c.zReal4.count x + [c.zpad].count x + [c.zdst0].count x + [c.zdst1].count x +
      K0.leafPad.count x + c.carry.count x + c.T1.count x + c.T2.count x + c.T5.count x := by
  have h1 : c.realAll = ([K0.core.cin] ++ c.bank) ++ c.dst ++ c.S ++ c.T ++ c.zReal4 ++
      ([c.zpad] ++ [c.zdst0] ++ [c.zdst1]) ++ K0.leafPad ++ c.carry ++ c.T1 ++ c.T2 ++ c.T5 := by
    simp only [SplitCfg.realAll, List.cons_append, List.nil_append]
  rw [h1]
  simp only [List.count_append]
  omega

/-- Exact postcondition of `c.make` on a clean initial state. -/
theorem cfg_make_correct (c : SplitCfg) (v : CfgValid c) (s : State) (m : List Bool)
    (hd0 : regValue c.dst s.basis = 0)
    (hT0 : regValue c.liveT s.basis = 0)
    (hSc0 : regValue c.cleanScratch s.basis = 0)
    (hi0 : s.basis K0.core.cin = false) :
    let a := regValue c.R.lo s.basis
    let b := regValue c.R.hi s.basis
    let u := run c.make m s
    u.phase = s.phase ∧
    regValue c.dst u.basis = (regValue c.bank s.basis) ^ 2 ∧
    regValue c.T u.basis = 2 * a * b ∧
    regValue c.T1 u.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) ∧
    regValue c.T2 u.basis = 2 * (b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h) ∧
    regValue c.T5 u.basis = 2 * ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) ∧
    ∀ q, q ∉ c.dst → q ∉ c.liveT → u.basis q = s.basis q := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  obtain ⟨nR, nR8, n1, n2, n5⟩ := cfg_nodups c v
  have sup := cfg_support c v; have hr := v.realNd
  have dj {A B : List Wire} (h : ∀ q, A.count q + B.count q ≤ c.realAll.count q) : ∀ q ∈ A, q ∉ B := kdis hr h
  have zOf (r : List Wire) (sub : ∀ q ∈ r, q ∈ c.cleanScratch) : regValue r s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hSc0 q (sub q hq))
  have zLive (r : List Wire) (sub : ∀ q ∈ r, q ∈ c.liveT) : regValue r s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hT0 q (sub q hq))
  have hS0 : regValue c.S s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hz40 : regValue c.zReal4 s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hpad0 : regValue K0.leafPad s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hcar0 : regValue c.carry s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hzpad0 : s.basis c.zpad = false := (regValue_zero _ _).mp hSc0 c.zpad (by simp [SplitCfg.cleanScratch])
  have hzd0 : s.basis c.zdst0 = false := (regValue_zero _ _).mp hSc0 c.zdst0 (by simp [SplitCfg.cleanScratch])
  have hzd1 : s.basis c.zdst1 = false := (regValue_zero _ _).mp hSc0 c.zdst1 (by simp [SplitCfg.cleanScratch])
  have hT_0 : regValue c.T s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have hT1_0 : regValue c.T1 s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have hT2_0 : regValue c.T2 s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have hT5_0 : regValue c.T5 s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have bv := c.R.bank_value wR s.basis
  obtain ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10⟩ := c.R.lens wR
  generalize ha : regValue c.R.lo s.basis = a
  generalize hb : regValue c.R.hi s.basis = b
  have aLt : a < 2 ^ 64 := by rw [← ha]; simpa [L0] using regValue_lt c.R.lo s.basis
  have bLt : b < 2 ^ (c.n - 64) := by
    rw [← hb]; have h := regValue_lt c.R.hi s.basis
    rw [L1, show c.R.bank.length = c.n from v.bankLen, show c.R.h = 64 from rfl] at h; exact h
  have realStep (P : Program) (hp : wires P ⊆ c.realAll.toFinset) : ∀ q ∈ wires P, q < 20000 :=
    fun q hq => v.realLt q (List.mem_toFinset.mp (hp hq))
  obtain ⟨a7, r8, e8⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ DI4Leaves.make c.Q2 (c.n=129) ++ c.R.smk ++
    DI4Leaves.make c.Q5 (c.n=128) ++ c.R.m6h ++ c.R.m7k ++ c.R.scl1591) c.R8.m8z m s
  obtain ⟨a6, r7, e7⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ DI4Leaves.make c.Q2 (c.n=129) ++ c.R.smk ++
    DI4Leaves.make c.Q5 (c.n=128) ++ c.R.m6h ++ c.R.m7k) c.R.scl1591 a7 s
  obtain ⟨a5, r6, e6⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ DI4Leaves.make c.Q2 (c.n=129) ++ c.R.smk ++
    DI4Leaves.make c.Q5 (c.n=128) ++ c.R.m6h) c.R.m7k a6 s
  obtain ⟨a4, r5, e5⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ DI4Leaves.make c.Q2 (c.n=129) ++ c.R.smk ++
    DI4Leaves.make c.Q5 (c.n=128)) c.R.m6h a5 s
  obtain ⟨a3, r4, e4⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ DI4Leaves.make c.Q2 (c.n=129) ++ c.R.smk)
    (DI4Leaves.make c.Q5 (c.n=128)) a4 s
  obtain ⟨a2, r3, e3⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ DI4Leaves.make c.Q2 (c.n=129)) c.R.smk a3 s
  obtain ⟨r1, r2, e2⟩ := kseq (LowZero18Diagonal.makeC c.Q1) (DI4Leaves.make c.Q2 (c.n=129)) a2 s
  dsimp only
  rw [SplitCfg.make, e8, e7, e6, e5, e4, e3, e2]
  have st1 := makeC_clean c.Q1 w1.1 w1.2 (Or.inl rfl) n1 s r1
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hd0 q (List.mem_of_mem_take h)))
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    hT1_0
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    hpad0
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_take h)))
    hi0
  generalize hs1 : run (LowZero18Diagonal.makeC c.Q1) r1 s = s1 at st1 ⊢
  have F1 : ∀ q, q ∉ c.R.dlo → q ∉ c.T1 → s1.basis q = s.basis q := st1.2.2.2
  have h_hi_bank (q : Wire) : c.R.hi.count q ≤ c.bank.count q := (List.drop_sublist 64 c.bank).count_le q
  have h_dhi_dst (q : Wire) : c.R.dhi.count q ≤ c.dst.count q := (List.drop_sublist 128 c.dst).count_le q
  have mLo {q : Wire} (h : q ∈ c.R.lo) : q ∈ c.bank := List.mem_of_mem_take (show q ∈ c.bank.take 64 from h)
  have mHi {q : Wire} (h : q ∈ c.R.hi) : q ∈ c.bank := List.mem_of_mem_drop (show q ∈ c.bank.drop 64 from h)
  have mDlo {q : Wire} (h : q ∈ c.R.dlo) : q ∈ c.dst := List.mem_of_mem_take (show q ∈ c.dst.take 128 from h)
  have mDhi {q : Wire} (h : q ∈ c.R.dhi) : q ∈ c.dst := List.mem_of_mem_drop (show q ∈ c.dst.drop 128 from h)
  have bLtR : b < 2 ^ (c.R.bank.length - c.R.h) := by simpa [SplitCfg.R, v.bankLen] using bLt
  have s1_T1 : regValue c.T1 s1.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) := by
    have h := st1.2.2.1; rw [c.Q1.lo_mod w1.1, c.Q1.hi_div w1.1] at h; simpa [SplitCfg.Q1, ha] using h
  have s1_dlo : regValue c.R.dlo s1.basis = a ^ 2 := by simpa [SplitCfg.Q1, ha] using st1.2.1
  have o_dlo {r : List Wire} (h : ∀ q, r.count q + c.dst.count q ≤ c.realAll.count q) : ∀ q ∈ r, q ∉ c.R.dlo :=
    fun q hq hd => dj h q hq (mDlo hd)
  have o_dhi {r : List Wire} (h : ∀ q, r.count q + c.dst.count q ≤ c.realAll.count q) : ∀ q ∈ r, q ∉ c.R.dhi :=
    fun q hq hd => dj h q hq (mDhi hd)
  have dlo_dhi : ∀ q ∈ c.R.dhi, q ∉ c.R.dlo := by
    intro q h1 h2
    have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
    rw [← List.take_append_drop 128 c.dst] at hnd
    exact (List.nodup_append.mp hnd).2.2 q h2 q h1 rfl
  have s1_keep (r : List Wire) (hd : ∀ q ∈ r, q ∉ c.R.dlo) (ht : ∀ q ∈ r, q ∉ c.T1) :
      regValue r s1.basis = regValue r s.basis := regValue_congr _ _ _ (fun q hq => F1 q (hd q hq) (ht q hq))
  have s1_eq (q : Wire) (hd : q ∉ c.dst) (ht : q ∉ c.T1) : s1.basis q = s.basis q :=
    F1 q (fun h => hd (mDlo h)) ht
  have s1_Q2_bank : regValue c.Q2.bank s1.basis = b := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q2, hn, if_true]
      rw [s1_keep _ (o_dlo (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega))
        (dj (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega)), hb]
    · simp only [SplitCfg.Q2, hn, if_false]
      rw [regValue_snoc_zero _ _ _ ((s1_eq c.zpad
        (dj (A := [c.zpad]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzpad0)]
      rw [s1_keep _ (o_dlo (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega))
        (dj (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega)), hb]
  have s1_Q2_dst0 : regValue c.Q2.dst s1.basis = 0 := by
    have hdhi0 : regValue c.R.dhi s1.basis = 0 :=
      (s1_keep _ dlo_dhi (dj (fun q => by clear * - c q h_dhi_dst; have := h_dhi_dst q; rw [realAll_count]; omega))).trans
        ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hd0 q (mDhi h)))
    by_cases hn : c.n = 128
    · simpa [SplitCfg.Q2, hn] using hdhi0
    · simp only [SplitCfg.Q2, hn, if_false, regValue_append, hdhi0, zero_add]
      have b0 : s1.basis c.zdst0 = false := (s1_eq _
        (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd0
      have b1 : s1.basis c.zdst1 = false := (s1_eq _
        (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd1
      simp [regValue, b0, b1]
  have s1_car0 : regValue c.carry s1.basis = 0 :=
    (s1_keep _ (o_dlo (fun q => by clear * - c q; rw [realAll_count]; omega))
      (dj (fun q => by clear * - c q; rw [realAll_count]; omega))).trans hcar0
  have s1_pad0 : regValue K0.leafPad s1.basis = 0 :=
    (s1_keep _ (o_dlo (fun q => by clear * - c q; rw [realAll_count]; omega))
      (dj (fun q => by clear * - c q; rw [realAll_count]; omega))).trans hpad0
  have s1_cin0 : s1.basis K0.core.cin = false :=
    (s1_eq _ (dj (A := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s1_T2_0 : regValue c.T2 s1.basis = 0 :=
    (s1_keep _ (o_dlo (fun q => by clear * - c q; rw [realAll_count]; omega))
      (dj (fun q => by clear * - c q; rw [realAll_count]; omega))).trans hT2_0
  have st2 := DI4Leaves.make_clean c.Q2 (c.n=129) w2.1 w2.2.1 w2.2.2 n2 s1 r2 (q2_pad_dims c v) (by intro hp; rw [s1_Q2_bank]; simpa only [hp] using bLt) s1_Q2_dst0
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s1_T2_0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s1_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s1_cin0)
  generalize hs2 : run (DI4Leaves.make c.Q2 (c.n=129)) r2 s1 = s2 at st2 ⊢
  have s2_dhi : regValue c.R.dhi s2.basis = b ^ 2 := by
    by_cases hn : c.n = 128
    · have h := st2.2.1; rw [s1_Q2_bank] at h; simpa [SplitCfg.Q2, hn] using h
    · have h := st2.2.1; rw [s1_Q2_bank] at h; simp only [SplitCfg.Q2, hn, if_false] at h
      have hlt : regValue (c.R.dhi ++ [c.zdst0, c.zdst1]) s2.basis < 2 ^ c.R.dhi.length := by
        rw [h, L3]; rcases v.hn with h128 | h129
        · exact absurd h128 hn
        · simp only [SplitCfg.R, v.bankLen, h129] at bLt ⊢
          have : b ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left bLt (by decide)
          simpa [← Nat.pow_mul] using this
      exact (regValue_snoc2_lt c.R.dhi c.zdst0 c.zdst1 s2.basis hlt).2.2.trans h
  have s2_zd0 : s2.basis c.zdst0 = false ∧ s2.basis c.zdst1 = false := by
    by_cases hn : c.n = 128
    · have f := st2.2.2.2
      have eq0 : s2.basis c.zdst0 = s1.basis c.zdst0 := f _ (by simp [SplitCfg.Q2, hn]; exact o_dhi (r := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
      have eq1 : s2.basis c.zdst1 = s1.basis c.zdst1 := f _ (by simp [SplitCfg.Q2, hn]; exact o_dhi (r := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
      exact ⟨eq0.trans ((s1_eq _ (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
        eq1.trans ((s1_eq _ (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
    · have h := st2.2.1; rw [s1_Q2_bank] at h; simp only [SplitCfg.Q2, hn, if_false] at h
      have hlt : regValue (c.R.dhi ++ [c.zdst0, c.zdst1]) s2.basis < 2 ^ c.R.dhi.length := by
        rw [h, L3]; rcases v.hn with h128 | h129
        · exact absurd h128 hn
        · simp only [SplitCfg.R, v.bankLen, h129] at bLt ⊢
          have : b ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left bLt (by decide)
          simpa [← Nat.pow_mul] using this
      have p := regValue_snoc2_lt c.R.dhi c.zdst0 c.zdst1 s2.basis hlt
      exact ⟨p.1, p.2.1⟩
  have s2_T2 : regValue c.T2 s2.basis = 2 * (b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h) := by
    have h := st2.2.2.1
    rw [c.Q2.lo_mod w2.1, c.Q2.hi_div w2.1, s1_Q2_bank] at h
    by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using h
  have F2 : ∀ q, q ∉ c.dst → q ∉ c.T1 → q ∉ c.T2 → s2.basis q = s.basis q := by
    intro q hd ht1 ht2
    by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
    · rcases hzd with rfl | rfl
      · exact s2_zd0.1.trans hzd0.symm
      · exact s2_zd0.2.trans hzd1.symm
    · have hq2d : q ∉ c.Q2.dst := by
        by_cases hn : c.n = 128
        · simp [SplitCfg.Q2, hn]; exact fun h => hd (mDhi h)
        · simp only [SplitCfg.Q2, hn, if_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | rfl | rfl)
          · exact hd (mDhi h)
          · exact hzd (Or.inl rfl)
          · exact hzd (Or.inr rfl)
      have hq2t : q ∉ c.Q2.T := by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using ht2
      exact (st2.2.2.2 q hq2d hq2t).trans (s1_eq q hd ht1)
  have s2_dlo : regValue c.R.dlo s2.basis = a ^ 2 := by
    rw [regValue_congr _ _ s1.basis (fun q hq => by
      have hnot_dhi : q ∉ c.R.dhi := fun h => dlo_dhi q h hq
      have hnot_z0 : q ≠ c.zdst0 := fun h => dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst0 (by simp) (h ▸ mDlo hq)
      have hnot_z1 : q ≠ c.zdst1 := fun h => dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst1 (by simp) (h ▸ mDlo hq)
      have hnot_t2 : q ∉ c.T2 := dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq)
      apply st2.2.2.2
      · by_cases hn : c.n = 128
        · simpa [SplitCfg.Q2, hn] using hnot_dhi
        · simp [SplitCfg.Q2, hn, hnot_dhi, hnot_z0, hnot_z1]
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using hnot_t2), s1_dlo]
  have s2_T1 : regValue c.T1 s2.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) := by
    rw [regValue_congr _ _ s1.basis (fun q hq => by
      have hnot_dst : q ∉ c.dst := fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q h hq
      have hnot_z0 : q ≠ c.zdst0 := fun h => dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst0 (by simp) (h ▸ hq)
      have hnot_z1 : q ≠ c.zdst1 := fun h => dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst1 (by simp) (h ▸ hq)
      have hnot_t2 : q ∉ c.T2 := dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq
      apply st2.2.2.2
      · by_cases hn : c.n = 128
        · simp [SplitCfg.Q2, hn]; exact fun h => hnot_dst (mDhi h)
        · simp [SplitCfg.Q2, hn, hnot_z0, hnot_z1]; exact fun h => hnot_dst (mDhi h)
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using hnot_t2), s1_T1]
  have sup_parts : (∀ q ∈ wires c.R.smk, q < 20000) ∧ (∀ q ∈ wires c.R.m6h, q < 20000) ∧
      (∀ q ∈ wires c.R.m7k, q < 20000) ∧ (∀ q ∈ wires c.R.scl1591, q < 20000) ∧
      (∀ q ∈ wires c.R8.m8z, q < 20000) := by
    have sm := sup.1
    simp only [SplitCfg.make, wires_append, Finset.union_subset_iff] at sm
    exact ⟨realStep _ sm.1.1.1.1.1.2, realStep _ sm.1.1.1.2, realStep _ sm.1.1.2, realStep _ sm.1.2, realStep _ sm.2⟩
  have mk_zh_z (t : State) (ht : ∀ q ∈ c.zReal4, t.basis q = false) : regValue c.R.z (zeroHigh t).basis = 0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    simp only [SplitCfg.R, List.mem_append] at hq
    rcases hq with hq | hq
    · simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]; exact ht q hq
    · simp only [zeroHigh, (List.mem_range'_1.mp hq).1, if_true]
  have st3_zh := c.R.smk_correct wR nR (zeroHigh s2) r3
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.S at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hS0 q hq)))
    (mk_zh_z s2 (fun q hq => (F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq)))
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq)))
    (by
      change (zeroHigh s2).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      exact (F2 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0)
  have loc3 := run_below20000 c.R.smk sup_parts.1 s2 r3
  generalize hs3 : run c.R.smk r3 s2 = s3 at loc3 ⊢
  have s3_F (q : Wire) (hS : q ∉ c.S) : s3.basis q = s2.basis q := by
    by_cases hq : q < 20000
    · rw [loc3.2 q hq, st3_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs3]; exact run_ge20000 c.R.smk sup_parts.1 s2 r3 q (Nat.le_of_not_lt hq)
  have s3_S : regValue c.S s3.basis = a + b := by
    have e1 := regValue_congr c.S s3.basis (run c.R.smk r3 (zeroHigh s2)).basis (fun q hq => loc3.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))
    rw [e1, show c.S = c.R.S from rfl, st3_zh.2.1]
    have elo : regValue c.R.lo (zeroHigh s2).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        exact F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s2).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        exact F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
    rw [elo, ehi]
  have F3 : ∀ q, q ∉ c.dst → q ∉ c.S → q ∉ c.T1 → q ∉ c.T2 → s3.basis q = s.basis q :=
    fun q hd hS ht1 ht2 => (s3_F q hS).trans (F2 q hd ht1 ht2)
  have s3_Q5_bank : regValue c.Q5.bank s3.basis = a + b := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true]
      rw [regValue_snoc_zero _ _ _ ((F3 c.zpad
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzpad0), s3_S]
    · simpa [SplitCfg.Q5, hn] using s3_S
  have s3_car0 : regValue c.carry s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hcar0
  have s3_T0 : regValue c.T s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT_0
  have s3_Q5_dst0 : regValue c.Q5.dst s3.basis = 0 := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true, regValue_append, s3_T0, zero_add]
      have b0 : s3.basis c.zdst0 = false := (F3 _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0
      have b1 : s3.basis c.zdst1 = false := (F3 _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1
      simp [regValue, b0, b1]
    · simpa [SplitCfg.Q5, hn] using s3_T0
  have s3_T5_0 : regValue c.T5 s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT5_0
  have s3_pad0 : regValue K0.leafPad s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hpad0
  have s3_cin0 : s3.basis K0.core.cin = false :=
    (F3 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have st4 := DI4Leaves.make_clean c.Q5 (c.n=128) w5.1 w5.2.1 (Or.inr w5.2.2) n5 s3 r4 (q5_pad_dims c v) (by intro hp; rw [s3_Q5_bank]; have hbb : b<2^64 := (by simpa only [hp] using bLt); norm_num at aLt hbb ⊢; omega) s3_Q5_dst0
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s3_T5_0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s3_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s3_cin0)
  generalize hs4 : run (DI4Leaves.make c.Q5 (c.n=128)) r4 s3 = s4 at st4 ⊢
  have s4_T : regValue c.T s4.basis = (a + b) ^ 2 := by
    by_cases hn : c.n = 128
    · have h := st4.2.1; rw [s3_Q5_bank] at h; simp only [SplitCfg.Q5, hn, if_true] at h
      have hlt : regValue (c.T ++ [c.zdst0, c.zdst1]) s4.basis < 2 ^ c.T.length := by
        rw [h, v.tLen, hn]; simp only [hn] at bLt
        have hab : a + b < 2 ^ 65 := by omega
        have : (a + b) ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left hab (by decide)
        simpa [← Nat.pow_mul] using this
      exact (regValue_snoc2_lt c.T c.zdst0 c.zdst1 s4.basis hlt).2.2.trans h
    · have h := st4.2.1; rw [s3_Q5_bank] at h; simpa [SplitCfg.Q5, hn] using h
  have s4_zd0 : s4.basis c.zdst0 = false ∧ s4.basis c.zdst1 = false := by
    by_cases hn : c.n = 128
    · have h := st4.2.1; rw [s3_Q5_bank] at h; simp only [SplitCfg.Q5, hn, if_true] at h
      have hlt : regValue (c.T ++ [c.zdst0, c.zdst1]) s4.basis < 2 ^ c.T.length := by
        rw [h, v.tLen, hn]; simp only [hn] at bLt
        have hab : a + b < 2 ^ 65 := by omega
        have : (a + b) ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left hab (by decide)
        simpa [← Nat.pow_mul] using this
      have p := regValue_snoc2_lt c.T c.zdst0 c.zdst1 s4.basis hlt
      exact ⟨p.1, p.2.1⟩
    · have eq0 : s4.basis c.zdst0 = s3.basis c.zdst0 := st4.2.2.2 _
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      have eq1 : s4.basis c.zdst1 = s3.basis c.zdst1 := st4.2.2.2 _
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      exact ⟨eq0.trans ((F3 _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
        eq1.trans ((F3 _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
  have s4_T5 : regValue c.T5 s4.basis = 2 * ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) := by
    have h := st4.2.2.1
    rw [c.Q5.lo_mod w5.1, c.Q5.hi_div w5.1, s3_Q5_bank, w5.2.2] at h
    by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using h
  have s4_F (q : Wire) (hT : q ∉ c.T) (hT5 : q ∉ c.T5) : s4.basis q = s3.basis q := by
    by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
    · rcases hzd with rfl | rfl
      · exact s4_zd0.1.trans ((F3 _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0).symm
      · exact s4_zd0.2.trans ((F3 _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1).symm
    · apply st4.2.2.2
      · by_cases hn : c.n = 128
        · simp only [SplitCfg.Q5, hn, if_true, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | rfl | rfl)
          · exact hT h
          · exact hzd (Or.inl rfl)
          · exact hzd (Or.inr rfl)
        · simpa [SplitCfg.Q5, hn] using hT
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using hT5
  have F4 : ∀ q, q ∉ c.dst → q ∉ c.S → q ∉ c.liveT → s4.basis q = s.basis q := by
    intro q hd hS hL
    have hT : q ∉ c.T := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT1 : q ∉ c.T1 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT2 : q ∉ c.T2 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT5 : q ∉ c.T5 := fun h => hL (by simp [SplitCfg.liveT, h])
    exact (s4_F q hT hT5).trans (F3 q hd hS hT1 hT2)
  have s4_dlo : regValue c.R.dlo (zeroHigh s4).basis = a ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDlo hq, true_or, or_true])), if_false]
      exact (s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))))).trans s2_dlo
  have s4_lo_zh : regValue c.R.lo (zeroHigh s4).basis = a :=
    (regValue_congr _ _ s.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
      exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mLo hq)))).trans ha
  have s4_hi_zh : regValue c.R.hi (zeroHigh s4).basis = b :=
    (regValue_congr _ _ s.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
      exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mHi hq)))).trans hb
  have s4_S_zh : regValue c.R.S (zeroHigh s4).basis = a + b :=
    (regValue_congr _ _ s3.basis (fun q hq => by
      change q ∈ c.S at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s3_S
  have s4_T_zh : regValue c.R.T (zeroHigh s4).basis = (a + b) ^ 2 :=
    (regValue_congr _ _ s4.basis (fun q hq => by
      change q ∈ c.T at hq; simp [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true]))])).trans s4_T
  have s4_car_zh : regValue c.R.carry (zeroHigh s4).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s4_cin_zh : (zeroHigh s4).basis c.R.cin = false := by
    change (zeroHigh s4).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0
  have s4_z_zh : regValue c.R.z (zeroHigh s4).basis = 0 := mk_zh_z s4 (fun q hq =>
    (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))
  have s4_zA_zh : regValue c.R.zA (zeroHigh s4).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s4_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have hTl := wR.T; have hSl := wR.S; have hhR := wR.hh; have h4R := wR.h4; have hclR := wR.carry
  have ex : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
  have sumLt : a + b < 2 ^ c.R.S.length := by
    have hp : 2 ^ c.R.h ≤ 2 ^ (c.R.bank.length - c.R.h) := Nat.pow_le_pow_right (by decide) (by clear * - hhR; omega)
    have hq : 2 ^ c.R.S.length = 2 * 2 ^ (c.R.bank.length - c.R.h) := by rw [hSl, pow_succ]; ring
    have haR : a < 2 ^ c.R.h := aLt
    clear * - haR bLtR hp hq; omega
  have sqLt : (a + b) ^ 2 < 2 ^ c.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have st5_zh : (run c.R.m6h r5 (zeroHigh s4)).phase = (zeroHigh s4).phase ∧
      regValue c.R.T (run c.R.m6h r5 (zeroHigh s4)).basis = 2 * a * b + b ^ 2 ∧
      ∀ q, q ∉ c.R.T → (run c.R.m6h r5 (zeroHigh s4)).basis q = (zeroHigh s4).basis q := by
    rw [c.R.m6h_square_run wR nR (zeroHigh s4) r5
      (fun q hq => (regValue_zero _ _).mp s4_car_zh q (List.mem_of_mem_take hq))
      s4_cin_zh a b aLt bLtR s4_T_zh s4_dlo s4_zA_zh s4_S_zh s4_lo_zh s4_hi_zh]
    unfold KRegs.m6
    obtain ⟨p, f, val⟩ := BalancedInverse.subInPlace_any_correct (c.R.dlo ++ c.R.zA) c.R.T
      (c.R.carry.take (c.R.T.length - 1)) c.R.cin
      (knd nR (fun q => by have := c.R.counts q; simp only [KRegs.all, List.count_cons, List.count_append]; omega))
      (by rw [List.length_append, L2, L6]; omega)
      (by rw [List.length_take]; omega)
      (zeroHigh s4) r5 (fun q hq => (regValue_zero _ _).mp s4_car_zh q (List.mem_of_mem_take hq))
    refine ⟨p, ?_, f⟩
    rw [val, regValue_append, s4_dlo, s4_zA_zh, s4_T_zh, s4_cin_zh]
    simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false, Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [ex]; omega) sqLt, ex]; omega
  have loc5 := run_below20000 c.R.m6h sup_parts.2.1 s4 r5
  generalize hs5 : run c.R.m6h r5 s4 = s5 at loc5 ⊢
  have s5_F (q : Wire) (hT : q ∉ c.T) : s5.basis q = s4.basis q := by
    by_cases hq : q < 20000
    · rw [loc5.2 q hq, st5_zh.2.2 q hT]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs5]; exact run_ge20000 c.R.m6h sup_parts.2.1 s4 r5 q (Nat.le_of_not_lt hq)
  have s5_T : regValue c.T s5.basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ _ (fun q hq => loc5.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st5_zh.2.1
  have s5_dhi : regValue c.R.dhi (zeroHigh s5).basis = b ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDhi hq, true_or, or_true])), if_false]
      exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
        ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
          (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))))).trans s2_dhi
  have s5_T_zh : regValue c.R.T (zeroHigh s5).basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ s5.basis (fun q hq => by
      change q ∈ c.T at hq; simp [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true]))])).trans s5_T
  have s5_car_zh : regValue c.R.carry (zeroHigh s5).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      rw [s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s5_cin_zh : (zeroHigh s5).basis c.R.cin = false := by
    change (zeroHigh s5).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    rw [s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))]
    exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0
  have s5_z_zh : regValue c.R.z (zeroHigh s5).basis = 0 := mk_zh_z s5 (fun q hq => by
    rw [s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
    exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))
  have s5_zB_zh : regValue c.R.zB (zeroHigh s5).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s5_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have xv5 : regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis = b ^ 2 := by
    rw [regValue_append, s5_dhi, s5_zB_zh]; simp
  have st6_zh : (run c.R.m7k r6 (zeroHigh s5)).phase = (zeroHigh s5).phase ∧
      regValue c.R.T (run c.R.m7k r6 (zeroHigh s5)).basis = 2 * a * b ∧
      ∀ q, q ∉ c.R.T → (run c.R.m7k r6 (zeroHigh s5)).basis q = (zeroHigh s5).basis q := by
    have hcl7 : ∀ q ∈ c.R.carry.take (c.R.T.length - 1), (zeroHigh s5).basis q = false :=
      fun q hq => (regValue_zero _ _).mp s5_car_zh q (List.mem_of_mem_take hq)
    have hnc7 : ((zeroHigh s5).basis ((c.R.dhi ++ c.R.zB).headD 0) && !(zeroHigh s5).basis (c.R.T.headD 0)) = false := by
      have hT := LowZero.head_bit c.R.T [] (zeroHigh s5).basis (c.R.T_ne wR)
      rw [List.append_nil] at hT
      rw [LowZero.head_bit c.R.dhi c.R.zB (zeroHigh s5).basis (c.R.dhi_ne wR), hT, s5_dhi, s5_T_zh,
        show 2 * a * b + b ^ 2 = b ^ 2 + 2 * (a * b) by ring, Nat.add_mul_mod_self_left]
      cases decide (b ^ 2 % 2 = 1) <;> rfl
    have h17 : (zeroHigh s5).basis ((c.R.dhi ++ c.R.zB).tail.headD 0) = false := by
      rw [KRegs.bit1 c.R.dhi c.R.zB (zeroHigh s5).basis (c.R.dhi_two wR), s5_dhi, KRegs.sq_bit1]; rfl
    have hA7 : c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis < 2 ^ (c.R.T.length - 1) :=
      fun _ => by rw [xv5, hTl, hSl]; exact KRegs.sq_trim_bound c.R.bank.length c.R.h b bLtR
    have hb7 : c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis ≤ regValue c.R.T (zeroHigh s5).basis % 2 ^ (c.R.T.length - 1) :=
      fun tc => by
        have tb := KRegs.trim_bound c.R.bank.length c.R.h a b tc aLt bLtR
        rw [xv5, s5_T_zh, hTl, hSl, Nat.mod_eq_of_lt tb]; omega
    have hab7 : a * b < 2 ^ c.R.bank.length := by
      have e : 2 ^ c.R.bank.length = 2 ^ c.R.h * 2 ^ (c.R.bank.length - c.R.h) := by rw [← pow_add]; congr 1; omega
      rw [e]; exact Nat.mul_lt_mul'' aLt bLtR
    have p2b : 2 ^ (c.R.bank.length + 1) = 2 * 2 ^ c.R.bank.length := by rw [pow_succ]; ring
    have HT : c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis < 2 ^ (c.R.T.length - 1) ∧
        regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis ≤ regValue c.R.T (zeroHigh s5).basis % 2 ^ (c.R.T.length - 1) ∧
        regValue c.R.T (zeroHigh s5).basis % 2 ^ (c.R.T.length - 1) < regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis + 2 ^ (c.R.T.length - 2) := by
      intro tc
      refine ⟨hA7 tc, hb7 tc, ?_⟩
      have tc' : 2 * c.R.h + 1 ≤ c.R.bank.length := tc
      have tb := KRegs.trim_bound c.R.bank.length c.R.h a b tc aLt bLtR
      have hpw : 2 ^ (c.R.bank.length + 1) ≤ 2 ^ (c.R.T.length - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [xv5, s5_T_zh, hTl, hSl, Nat.mod_eq_of_lt tb]
      rw [hTl, hSl] at hpw
      rw [show 2 * a * b + b ^ 2 = 2 * (a * b) + b ^ 2 by ring]; omega
    have HF : ¬c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis ≤ regValue c.R.T (zeroHigh s5).basis ∧
        regValue c.R.T (zeroHigh s5).basis < regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis + 2 ^ (c.R.T.length - 1) := by
      intro _
      have hpw : 2 ^ (c.R.bank.length + 1) ≤ 2 ^ (c.R.T.length - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [xv5, s5_T_zh, show 2 * a * b + b ^ 2 = 2 * (a * b) + b ^ 2 by ring]
      constructor <;> omega
    rw [c.R.m7k_run wR nR (zeroHigh s5) r6 hcl7 hnc7 s5_cin_zh h17 HT HF]
    obtain ⟨p, f, val⟩ := c.R.m7t_correct wR nR (zeroHigh s5) r6 hcl7 hnc7 s5_cin_zh h17 hA7 hb7
    refine ⟨p, ?_, f⟩
    rw [val, xv5, s5_T_zh, s5_cin_zh]
    simp only [Bool.toNat_false, Nat.sub_zero]
    rw [ksubmod _ _ _ (by omega) (by rw [ex] at sqLt; omega)]; omega
  have loc6 := run_below20000 c.R.m7k sup_parts.2.2.1 s5 r6
  generalize hs6 : run c.R.m7k r6 s5 = s6 at loc6 ⊢
  have s6_F (q : Wire) (hT : q ∉ c.T) : s6.basis q = s5.basis q := by
    by_cases hq : q < 20000
    · rw [loc6.2 q hq, st6_zh.2.2 q hT]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs6]; exact run_ge20000 c.R.m7k sup_parts.2.2.1 s5 r6 q (Nat.le_of_not_lt hq)
  have s6_T : regValue c.T s6.basis = 2 * a * b :=
    (regValue_congr _ _ _ (fun q hq => loc6.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st6_zh.2.1
  have s6_S_zh : regValue c.R.S (zeroHigh s6).basis = regValue c.R.lo (zeroHigh s6).basis + regValue c.R.hi (zeroHigh s6).basis := by
    have eS : regValue c.R.S (zeroHigh s6).basis = a + b :=
      (regValue_congr _ _ s3.basis (fun q hq => by
        change q ∈ c.S at hq
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
        exact (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
          ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
            (s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
              (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))))).trans s3_S
    have elo : regValue c.R.lo (zeroHigh s6).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)),
          s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))]
        exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mLo hq)))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s6).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)),
          s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))]
        exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mHi hq)))).trans hb
    rw [eS, elo, ehi]
  have st7_zh := c.R.scl1591_correct wR nR (zeroHigh s6) r7 s6_S_zh
    (mk_zh_z s6 (fun q hq => by
      rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq)))
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq)))
    (by
      change (zeroHigh s6).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      rw [s6_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp)),
        s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))]
      exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0)
  have loc7 := run_below20000 c.R.scl1591 sup_parts.2.2.2.1 s6 r7
  generalize hs7 : run c.R.scl1591 r7 s6 = s7 at loc7 ⊢
  have s7_F (q : Wire) (hS : q ∉ c.S) : s7.basis q = s6.basis q := by
    by_cases hq : q < 20000
    · rw [loc7.2 q hq, st7_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs7]; exact run_ge20000 c.R.scl1591 sup_parts.2.2.2.1 s6 r7 q (Nat.le_of_not_lt hq)
  have s7_S0 : regValue c.S s7.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => loc7.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st7_zh.2.1
  have s7_dlo : regValue c.R8.dlo s7.basis = a ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq =>
      (s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq)))))))).trans s2_dlo
  have s7_dhi : regValue c.R8.dhi s7.basis = b ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq =>
      (s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))))))).trans s2_dhi
  have s7_T : regValue c.R8.T s7.basis = 2 * a * b :=
    (regValue_congr _ _ s6.basis (fun q hq => by
      change q ∈ c.T at hq
      exact s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s6_T
  have s7_z8 : regValue c.R8.z s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s7_S0 q (List.mem_of_mem_take (show q ∈ c.S.take 62 from hq)))
  have s7_zM : regValue c.R8.zM s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s7_z8 q (List.mem_of_mem_take (show q ∈ c.R8.z.take _ from hq)))
  have s7_car : regValue c.R8.carry s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      rw [s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s7_cin : s7.basis c.R8.cin = false := by
    change s7.basis K0.core.cin = false
    rw [s7_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp)),
      s6_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp)),
      s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))]
    exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0
  obtain ⟨p8, f8, v8⟩ := c.R8.m8z_correct wR8 nR8 s7 r8 (a * b)
    (fun q hq => (regValue_zero _ _).mp s7_car q (List.mem_of_mem_take hq))
    (by rw [s7_T]; ring) s7_cin
  generalize hs8 : run c.R8.m8z r8 s7 = s8 at p8 f8 v8 ⊢
  have s8_F (q : Wire) (hd : q ∉ c.dst) : s8.basis q = s7.basis q :=
    f8 q (fun h => hd (List.mem_of_mem_drop (show q ∈ c.dst.drop 64 from h)))
  have st8_dmid : regValue c.R8.dmid s8.basis = 2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2) := by
    have hm := dmid_val c v s7.basis; rw [s7_dlo, s7_dhi] at hm
    rw [v8, regValue_append, s7_T, s7_zM, hm, s7_cin]
    simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false]
    apply Nat.mod_eq_of_lt
    have bv64 : regValue c.R.bank s.basis = a + 2 ^ 64 * b := by
      simpa only [show c.R.h = 64 from rfl, ha, hb] using bv
    have hlt : a + 2 ^ 64 * b < 2 ^ c.n := by
      have hbl : c.n = c.R.bank.length := v.bankLen.symm
      rw [← bv64, hbl]; exact regValue_lt c.R.bank s.basis
    have hsq : (a + 2 ^ 64 * b) ^ 2 < 2 ^ (2 * c.n) := by
      have := Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0); simpa [← Nat.pow_mul, Nat.mul_comm] using this
    have hle : 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) ≤ (a + 2 ^ 64 * b) ^ 2 := by
      have h1 : 2 ^ 64 * (a ^ 2 / 2 ^ 64) ≤ a ^ 2 := Nat.mul_div_le (a ^ 2) (2 ^ 64)
      have h2 : (a + 2 ^ 64 * b) ^ 2 = a ^ 2 + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
      have h3 : 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) =
          2 ^ 64 * (a ^ 2 / 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
      rw [h2, h3]; exact Nat.add_le_add_right h1 _
    have hdmid : c.R8.dmid.length = 2 * c.n - 64 := by simp [KRegs.dmid, SplitCfg.R8, v.dstLen]
    rw [hdmid]
    have hpow : 2 ^ 64 * 2 ^ (2 * c.n - 64) = 2 ^ (2 * c.n) := by rw [← Nat.pow_add]; congr 1; rcases v.hn with h | h <;> omega
    exact Nat.lt_of_mul_lt_mul_left (hpow.symm ▸ Nat.lt_of_le_of_lt hle hsq)
  refine ⟨p8.trans (loc7.1.trans (st7_zh.1.trans (loc6.1.trans (st6_zh.1.trans (loc5.1.trans (st5_zh.1.trans (st4.1.trans (loc3.1.trans (st3_zh.1.trans (st2.1.trans st1.1)))))))))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hsplit := regValue_append (c.dst.take 64) c.R8.dmid s8.basis
    rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst] at hsplit
    have hlo64 : regValue (c.dst.take 64) s8.basis = a ^ 2 % 2 ^ 64 := by
      have e : regValue (c.dst.take 64) s8.basis = regValue (c.dst.take 64) s7.basis :=
        regValue_congr _ _ _ (fun q hq => by
          apply f8
          have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
          rw [← List.take_append_drop 64 c.dst] at hnd
          exact fun hm => (List.nodup_append.mp hnd).2.2 q hq q hm rfl)
      rw [e, show c.dst.take 64 = c.R8.dlo.take 64 from by simp [KRegs.dlo, SplitCfg.R8, List.take_take],
        regValue_take_mod c.R8.dlo 64 (by simp [KRegs.dlo, SplitCfg.R8, v.dstLen]; rcases v.hn with h | h <;> omega), s7_dlo]
    have hlen64 : (c.dst.take 64).length = 64 := by simp [v.dstLen]; rcases v.hn with h | h <;> omega
    have bv64 : regValue c.R.bank s.basis = a + 2 ^ 64 * b := by
      simpa only [show c.R.h = 64 from rfl, ha, hb] using bv
    rw [hsplit, hlen64, hlo64, st8_dmid, show c.bank = c.R.bank from rfl, bv64]
    have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
    have hring : a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) =
        (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
    rw [hring, hdiv]; ring
  · exact (regValue_congr _ _ s7.basis (fun q hq => s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s7_T
  · exact (regValue_congr _ _ s2.basis (fun q hq =>
      (s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))))))).trans s2_T1
  · exact (regValue_congr _ _ s2.basis (fun q hq =>
      (s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))))))).trans s2_T2
  · exact (regValue_congr _ _ s4.basis (fun q hq =>
      (s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))))).trans s4_T5
  · intro q hd hL
    have hT : q ∉ c.T := fun h => hL (by simp [SplitCfg.liveT, h])
    rw [s8_F q hd]
    by_cases hS : q ∈ c.S
    · exact ((regValue_zero _ _).mp s7_S0 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
    · exact (s7_F q hS).trans ((s6_F q hT).trans ((s5_F q hT).trans (F4 q hd hS hL)))

/-- Exact postcondition of `c.clear` restoring `dst` and `liveT` to 0. -/
theorem cfg_clear_correct (c : SplitCfg) (v : CfgValid c) (s : State) (m : List Bool)
    (hd0 : regValue c.dst s.basis = (regValue c.bank s.basis) ^ 2)
    (hT : regValue c.T s.basis = 2 * regValue c.R.lo s.basis * regValue c.R.hi s.basis)
    (hT1 : regValue c.T1 s.basis = 2 * (regValue c.R.lo s.basis % 2 ^ 32) * (regValue c.R.lo s.basis / 2 ^ 32))
    (hT2 : regValue c.T2 s.basis = 2 * (regValue c.R.hi s.basis % 2 ^ c.Q2.h) * (regValue c.R.hi s.basis / 2 ^ c.Q2.h))
    (hT5 : regValue c.T5 s.basis = 2 * ((regValue c.R.lo s.basis + regValue c.R.hi s.basis) % 2 ^ 33) *
      ((regValue c.R.lo s.basis + regValue c.R.hi s.basis) / 2 ^ 33))
    (hSc0 : regValue c.cleanScratch s.basis = 0)
    (hi0 : s.basis K0.core.cin = false) :
    let u := run c.clear m s
    u.phase = s.phase ∧
    regValue c.dst u.basis = 0 ∧
    regValue c.liveT u.basis = 0 ∧
    ∀ q, q ∉ c.dst → q ∉ c.liveT → u.basis q = s.basis q := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  obtain ⟨nR, nR8, n1, n2, n5⟩ := cfg_nodups c v
  have sup := cfg_support c v; have hr := v.realNd
  have dj {A B : List Wire} (h : ∀ q, A.count q + B.count q ≤ c.realAll.count q) : ∀ q ∈ A, q ∉ B := kdis hr h
  have zOf (r : List Wire) (sub : ∀ q ∈ r, q ∈ c.cleanScratch) : regValue r s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hSc0 q (sub q hq))
  have hS0 : regValue c.S s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hz40 : regValue c.zReal4 s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hpad0 : regValue K0.leafPad s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hcar0 : regValue c.carry s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hzpad0 : s.basis c.zpad = false := (regValue_zero _ _).mp hSc0 c.zpad (by simp [SplitCfg.cleanScratch])
  have hzd0 : s.basis c.zdst0 = false := (regValue_zero _ _).mp hSc0 c.zdst0 (by simp [SplitCfg.cleanScratch])
  have hzd1 : s.basis c.zdst1 = false := (regValue_zero _ _).mp hSc0 c.zdst1 (by simp [SplitCfg.cleanScratch])
  have bv := c.R.bank_value wR s.basis
  obtain ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10⟩ := c.R.lens wR
  generalize ha : regValue c.R.lo s.basis = a at hT hT1 hT5 ⊢
  generalize hb : regValue c.R.hi s.basis = b at hT hT2 hT5 ⊢
  have aLt : a < 2 ^ 64 := by as_aux_lemma => rw [← ha]; simpa [L0] using regValue_lt c.R.lo s.basis
  have bLt : b < 2 ^ (c.n - 64) := by
    as_aux_lemma =>
      rw [← hb]; have h := regValue_lt c.R.hi s.basis
      rw [L1, show c.R.bank.length = c.n from v.bankLen, show c.R.h = 64 from rfl] at h; exact h
  have realStep (P : Program) (hp : wires P ⊆ c.realAll.toFinset) : ∀ q ∈ wires P, q < 20000 :=
    fun q hq => v.realLt q (List.mem_toFinset.mp (hp hq))
  have sup_parts : (∀ q ∈ wires (DI4Merge.safe c.R8), q < 20000) ∧ (∀ q ∈ wires c.R.smkT, q < 20000) ∧
      (∀ q ∈ wires c.R.c7t, q < 20000) ∧ (∀ q ∈ wires c.R.c6h, q < 20000) ∧
      (∀ q ∈ wires c.R.scl1591, q < 20000) := by
    as_aux_lemma =>
      have sc := sup.2
      simp only [SplitCfg.clear, wires_append, Finset.union_subset_iff] at sc
      exact ⟨realStep _ sc.1.1.1.1.1.1.1, realStep _ sc.1.1.1.1.1.1.2, realStep _ sc.1.1.1.1.1.2,
        realStep _ sc.1.1.1.1.2, realStep _ sc.1.1.2⟩
  obtain ⟨a7, r8, e8⟩ := kseq ((DI4Merge.safe c.R8) ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    DI4Leaves.clear c.Q5 (c.n=128) ++ c.R.scl1591 ++ DI4Leaves.clear c.Q2 (c.n=129))
    (DI4Square.clearC c.Q1) m s
  obtain ⟨a6, r7, e7⟩ := kseq ((DI4Merge.safe c.R8) ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    DI4Leaves.clear c.Q5 (c.n=128) ++ c.R.scl1591) (DI4Leaves.clear c.Q2 (c.n=129)) a7 s
  obtain ⟨a5, r6, e6⟩ := kseq ((DI4Merge.safe c.R8) ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    DI4Leaves.clear c.Q5 (c.n=128)) c.R.scl1591 a6 s
  obtain ⟨a4, r5, e5⟩ := kseq ((DI4Merge.safe c.R8) ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h)
    (DI4Leaves.clear c.Q5 (c.n=128)) a5 s
  obtain ⟨a3, r4, e4⟩ := kseq ((DI4Merge.safe c.R8) ++ c.R.smkT ++ c.R.c7t) c.R.c6h a4 s
  obtain ⟨a2, r3, e3⟩ := kseq ((DI4Merge.safe c.R8) ++ c.R.smkT) c.R.c7t a3 s
  obtain ⟨r1, r2, e2⟩ := kseq (DI4Merge.safe c.R8) c.R.smkT a2 s
  dsimp only
  rw [SplitCfg.clear, e8, e7, e6, e5, e4, e3, e2]
  have mLo {q : Wire} (h : q ∈ c.R.lo) : q ∈ c.bank := List.mem_of_mem_take (show q ∈ c.bank.take 64 from h)
  have mHi {q : Wire} (h : q ∈ c.R.hi) : q ∈ c.bank := List.mem_of_mem_drop (show q ∈ c.bank.drop 64 from h)
  have mDlo {q : Wire} (h : q ∈ c.R.dlo) : q ∈ c.dst := List.mem_of_mem_take (show q ∈ c.dst.take 128 from h)
  have mDhi {q : Wire} (h : q ∈ c.R.dhi) : q ∈ c.dst := List.mem_of_mem_drop (show q ∈ c.dst.drop 128 from h)
  have bLtR : b < 2 ^ (c.R.bank.length - c.R.h) := by as_aux_lemma => simpa [SplitCfg.R, v.bankLen] using bLt
  have hTl := wR.T; have hSl := wR.S; have hhR := wR.hh; have h4R := wR.h4; have hclR := wR.carry
  have ex : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by as_aux_lemma => ring
  have sumLt : a + b < 2 ^ c.R.S.length := by
    as_aux_lemma =>
      have hp : 2 ^ c.R.h ≤ 2 ^ (c.R.bank.length - c.R.h) := Nat.pow_le_pow_right (by decide) (by clear * - hhR; omega)
      have hq : 2 ^ c.R.S.length = 2 * 2 ^ (c.R.bank.length - c.R.h) := by rw [hSl, pow_succ]; ring
      have haR : a < 2 ^ c.R.h := aLt
      clear * - haR bLtR hp hq; omega
  have sqLt : (a + b) ^ 2 < 2 ^ c.R.T.length := by as_aux_lemma => rw [hTl]; exact square_bound _ _ sumLt
  have bv64 : regValue c.R.bank s.basis = a + 2 ^ 64 * b := by
    as_aux_lemma =>
      simpa only [show c.R.h = 64 from rfl, ha, hb] using bv
  have hdmid_init : regValue c.R8.dmid s.basis = 2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2) := by
    as_aux_lemma =>
      have hsplit := regValue_append (c.dst.take 64) c.R8.dmid s.basis
      rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst] at hsplit
      have hlen64 : (c.dst.take 64).length = 64 := by simp [v.dstLen]; rcases v.hn with h | h <;> omega
      rw [hsplit, hlen64, show c.bank = c.R.bank from rfl, bv64] at hd0
      have hlt64 : regValue (c.dst.take 64) s.basis < 2 ^ 64 := by have := regValue_lt (c.dst.take 64) s.basis; rwa [hlen64] at this
      have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
      have hmod_lt : a ^ 2 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
      have hsq : (a + 2 ^ 64 * b) ^ 2 = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by
        calc (a + 2 ^ 64 * b) ^ 2 = a ^ 2 + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
        _ = (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by rw [hdiv]
        _ = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by ring
      rw [hsq] at hd0
      have hdivq := congrArg (· / 2 ^ 64) hd0
      dsimp only at hdivq
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64), Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64),
        Nat.div_eq_of_lt hlt64, Nat.div_eq_of_lt hmod_lt] at hdivq
      simpa only [Nat.zero_add] using hdivq
  obtain ⟨p1, f1, v1⟩ := c.R8.c8z_correct wR8 nR8 s r1
    (fun q hq => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_take hq))
    (by
      rw [LowZero.head_false_of_even c.R8.T c.R8.zM s.basis (a * b)
        (by rw [show c.R8.T = c.T from rfl, hT]; ring) (c.R8.T_ne wR8)]
      rfl)
    hi0
  have hMerge : run (DI4Merge.safe c.R8) r1 s=run c.R8.c8z r1 s := by
    rw [← DI4Merge.c8g_eq_c8z c.R8 wR8]
    apply DI4Merge.safe_eq c.R8 wR8 nR8 s r1
    · exact hd0
    · change regValue c.T s.basis=2*regValue c.R.lo s.basis*regValue c.R.hi s.basis
      rw [ha,hb]
      exact hT
    · exact KRegs.xz hS0 (fun q hq => List.mem_of_mem_take hq)
    · exact hcar0
    · exact hi0
  rw [← hMerge] at p1 f1 v1
  generalize hs1 : run (DI4Merge.safe c.R8) r1 s = s1 at p1 f1 v1 ⊢
  have s1_F (q : Wire) (hd : q ∉ c.dst) : s1.basis q = s.basis q :=
    f1 q (fun h => hd (List.mem_of_mem_drop (show q ∈ c.dst.drop 64 from h)))
  have st1_dmid : regValue c.R8.dmid s1.basis = a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2 := by
    as_aux_lemma =>
      have s_zM : regValue c.R8.zM s.basis = 0 :=
        (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hS0 q
          (List.mem_of_mem_take (show q ∈ c.S.take 62 from List.mem_of_mem_take (show q ∈ c.R8.z.take _ from hq))))
      have hlt : 2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2) < 2 ^ c.R8.dmid.length := by
        rw [← hdmid_init]; exact regValue_lt c.R8.dmid s.basis
      rw [v1, regValue_append, show c.R8.T = c.T from rfl, hT, s_zM, hdmid_init, show c.R8.cin = K0.core.cin from rfl, hi0]
      simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false, Nat.sub_zero]
      rw [ksubmod _ _ _ (Nat.le_add_right _ _) hlt]
      exact Nat.add_sub_cancel_left _ _
  have s1_dst_eq : regValue c.dst s1.basis = a ^ 2 + 2 ^ 128 * b ^ 2 := by
    as_aux_lemma =>
      have hsplit := regValue_append (c.dst.take 64) c.R8.dmid s1.basis
      rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst] at hsplit
      have hlen64 : (c.dst.take 64).length = 64 := by simp [v.dstLen]; rcases v.hn with h | h <;> omega
      have hlo64 : regValue (c.dst.take 64) s1.basis = a ^ 2 % 2 ^ 64 := by
        have e : regValue (c.dst.take 64) s1.basis = regValue (c.dst.take 64) s.basis :=
          regValue_congr _ _ _ (fun q hq => by
            apply f1
            have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
            rw [← List.take_append_drop 64 c.dst] at hnd
            exact fun hm => (List.nodup_append.mp hnd).2.2 q hq q hm rfl)
        rw [e]
        have hsp := regValue_append (c.dst.take 64) c.R8.dmid s.basis
        rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst, hlen64] at hsp
        rw [hsp, hdmid_init, show c.bank = c.R.bank from rfl, bv64] at hd0
        have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
        have hsq : (a + 2 ^ 64 * b) ^ 2 = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by
          calc (a + 2 ^ 64 * b) ^ 2 = a ^ 2 + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
          _ = (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by rw [hdiv]
          _ = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by ring
        rw [hsq] at hd0
        exact Nat.add_right_cancel hd0
      rw [hsplit, hlen64, hlo64, st1_dmid]
      have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
      calc a ^ 2 % 2 ^ 64 + 2 ^ 64 * (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)
          = (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 128 * b ^ 2 := by ring
        _ = a ^ 2 + 2 ^ 128 * b ^ 2 := by rw [hdiv]
  have s1_dlo : regValue c.R.dlo s1.basis = a ^ 2 := by
    as_aux_lemma =>
      have h128 := regValue_append c.R.dlo c.R.dhi s1.basis
      rw [show c.R.dlo ++ c.R.dhi = c.dst from List.take_append_drop 128 c.dst, L2, show c.R.h = 64 from rfl, s1_dst_eq] at h128
      have ha2 : a ^ 2 < 2 ^ 128 := by have := Nat.pow_lt_pow_left aLt (by decide : 2 ≠ 0); simpa [← Nat.pow_mul] using this
      have hdloLt : regValue c.R.dlo s1.basis < 2 ^ 128 := by have := regValue_lt c.R.dlo s1.basis; rwa [L2, show c.R.h = 64 from rfl] at this
      have hmod := congrArg (· % 2 ^ 128) h128
      dsimp only at hmod
      rw [show (2 : Nat) ^ (2 * 64) = 2 ^ 128 from rfl,
        Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdloLt, Nat.mod_eq_of_lt ha2] at hmod
      exact hmod.symm
  have s1_dhi : regValue c.R.dhi s1.basis = b ^ 2 := by
    as_aux_lemma =>
      have h128 := regValue_append c.R.dlo c.R.dhi s1.basis
      rw [show c.R.dlo ++ c.R.dhi = c.dst from List.take_append_drop 128 c.dst, L2, show c.R.h = 64 from rfl,
        show (2 : Nat) ^ (2 * 64) = 2 ^ 128 from rfl, s1_dst_eq, s1_dlo] at h128
      exact (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2 ^ 128) (Nat.add_left_cancel h128)).symm
  have mk_zh_z (t : State) (ht : ∀ q ∈ c.zReal4, t.basis q = false) : regValue c.R.z (zeroHigh t).basis = 0 := by
    as_aux_lemma =>
      apply (regValue_zero _ _).mpr; intro q hq
      simp only [SplitCfg.R, List.mem_append] at hq
      rcases hq with hq | hq
      · simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]; exact ht q hq
      · simp only [zeroHigh, (List.mem_range'_1.mp hq).1, if_true]
  have s1_T_zh : regValue c.R.T (zeroHigh s1).basis = 2 * regValue c.R.lo (zeroHigh s1).basis * regValue c.R.hi (zeroHigh s1).basis := by
    as_aux_lemma =>
      have eT : regValue c.R.T (zeroHigh s1).basis = 2 * a * b :=
        (regValue_congr _ _ s.basis (fun q hq => by
          change q ∈ c.T at hq
          simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
          exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT
      have elo : regValue c.R.lo (zeroHigh s1).basis = a :=
        (regValue_congr _ _ s.basis (fun q hq => by
          simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
          exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
      have ehi : regValue c.R.hi (zeroHigh s1).basis = b :=
        (regValue_congr _ _ s.basis (fun q hq => by
          simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
          exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
      rw [eT, elo, ehi]
  have s1_S0_zh : regValue c.R.S (zeroHigh s1).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.S at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hS0 q hq))
  have s1_car0_zh : regValue c.R.carry (zeroHigh s1).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s1_cin0_zh : (zeroHigh s1).basis c.R.cin = false := by
    as_aux_lemma =>
      change (zeroHigh s1).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      exact (s1_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s1_z0_zh : regValue c.R.z (zeroHigh s1).basis = 0 :=
    mk_zh_z s1 (fun q hq => (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))
  have smkT_eq := c.R.smkT_run wR nR (zeroHigh s1) r2 s1_T_zh s1_S0_zh s1_cin0_zh
  have st2_zh := c.R.smk_correct wR nR (zeroHigh s1) r2 s1_S0_zh s1_z0_zh s1_car0_zh s1_cin0_zh
  rw [← smkT_eq] at st2_zh
  have loc2 := run_below20000 c.R.smkT sup_parts.2.1 s1 r2
  generalize hs2 : run c.R.smkT r2 s1 = s2 at loc2 ⊢
  have s2_F (q : Wire) (hS : q ∉ c.S) : s2.basis q = s1.basis q := by
    as_aux_lemma =>
      by_cases hq : q < 20000
      · rw [loc2.2 q hq, st2_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
      · rw [← hs2]; exact run_ge20000 c.R.smkT sup_parts.2.1 s1 r2 q (Nat.le_of_not_lt hq)
  have s2_S : regValue c.S s2.basis = a + b := by
    as_aux_lemma =>
      have e1 := regValue_congr c.S s2.basis (run c.R.smkT r2 (zeroHigh s1)).basis
        (fun q hq => loc2.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))
      rw [e1, show c.S = c.R.S from rfl, st2_zh.2.1]
      have elo : regValue c.R.lo (zeroHigh s1).basis = a :=
        (regValue_congr _ _ s.basis (fun q hq => by
          simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
          exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
      have ehi : regValue c.R.hi (zeroHigh s1).basis = b :=
        (regValue_congr _ _ s.basis (fun q hq => by
          simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
          exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
      rw [elo, ehi]
  have s2_dhi_zh : regValue c.R.dhi (zeroHigh s2).basis = b ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDhi hq, true_or, or_true])), if_false]
      exact s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))).trans s1_dhi
  have s2_T_zh : regValue c.R.T (zeroHigh s2).basis = 2 * a * b :=
    (regValue_congr _ _ s.basis (fun q hq => by
      change q ∈ c.T at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))).trans hT
  have s2_z_zh : regValue c.R.z (zeroHigh s2).basis = 0 :=
    mk_zh_z s2 (fun q hq => (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq)))
  have s2_zB_zh : regValue c.R.zB (zeroHigh s2).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s2_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have s2_car_zh : regValue c.R.carry (zeroHigh s2).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq)))
  have s2_cin_zh : (zeroHigh s2).basis c.R.cin = false := by
    as_aux_lemma =>
      change (zeroHigh s2).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      exact (s2_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s1_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0)
  have xv2 : regValue (c.R.dhi ++ c.R.zB) (zeroHigh s2).basis = b ^ 2 := by
    as_aux_lemma =>
      rw [regValue_append, s2_dhi_zh, s2_zB_zh]; simp
  have st3_zh : (run c.R.c7t r3 (zeroHigh s2)).phase = (zeroHigh s2).phase ∧
      regValue c.R.T (run c.R.c7t r3 (zeroHigh s2)).basis = 2 * a * b + b ^ 2 ∧
      ∀ q, q ∉ c.R.T → (run c.R.c7t r3 (zeroHigh s2)).basis q = (zeroHigh s2).basis q := by
    as_aux_lemma =>
      obtain ⟨p, f, val⟩ := c.R.c7t_correct wR nR (zeroHigh s2) r3
        (fun q hq => (regValue_zero _ _).mp s2_car_zh q (List.mem_of_mem_take hq))
        (by
          have hT' := LowZero.head_false_of_even c.R.T [] (zeroHigh s2).basis (a * b) (by rw [s2_T_zh]; ring) (c.R.T_ne wR)
          rw [List.append_nil] at hT'
          rw [hT']; exact Bool.and_false _)
        s2_cin_zh
        (by rw [KRegs.bit1 c.R.dhi c.R.zB (zeroHigh s2).basis (c.R.dhi_two wR), s2_dhi_zh, KRegs.sq_bit1]; rfl)
        (fun _ => by rw [xv2, hTl, hSl]; exact KRegs.sq_trim_bound c.R.bank.length c.R.h b bLtR)
        (fun tc => by
          have tb := KRegs.trim_bound c.R.bank.length c.R.h a b tc aLt bLtR
          rw [xv2, s2_T_zh, hTl, hSl, Nat.mod_eq_of_lt (by clear * - tb; omega)]; clear * - tb; omega)
      refine ⟨p, ?_, f⟩
      rw [val, xv2, s2_T_zh, s2_cin_zh]
      simp only [Bool.toNat_false, Nat.add_zero]
      rw [Nat.mod_eq_of_lt (by clear * - ex sqLt; omega)]; ring
  have loc3 := run_below20000 c.R.c7t sup_parts.2.2.1 s2 r3
  generalize hs3 : run c.R.c7t r3 s2 = s3 at loc3 ⊢
  have s3_F (q : Wire) (hT' : q ∉ c.T) : s3.basis q = s2.basis q := by
    as_aux_lemma =>
      by_cases hq : q < 20000
      · rw [loc3.2 q hq, st3_zh.2.2 q hT']; simp [zeroHigh, Nat.not_le.mpr hq]
      · rw [← hs3]; exact run_ge20000 c.R.c7t sup_parts.2.2.1 s2 r3 q (Nat.le_of_not_lt hq)
  have s3_T : regValue c.T s3.basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ _ (fun q hq => loc3.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st3_zh.2.1
  have s3_dlo_zh : regValue c.R.dlo (zeroHigh s3).basis = a ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDlo hq, true_or, or_true])), if_false]
      exact (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))))).trans s1_dlo
  have s3_T_zh : regValue c.R.T (zeroHigh s3).basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ s3.basis (fun q hq => by
      change q ∈ c.T at hq; simp [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true]))])).trans s3_T
  have s3_z_zh : regValue c.R.z (zeroHigh s3).basis = 0 :=
    mk_zh_z s3 (fun q hq => (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))))
  have s3_zA_zh : regValue c.R.zA (zeroHigh s3).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s3_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have s3_car_zh : regValue c.R.carry (zeroHigh s3).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))))
  have s3_cin_zh : (zeroHigh s3).basis c.R.cin = false := by
    as_aux_lemma =>
      change (zeroHigh s3).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      exact (s3_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s2_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s1_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0))
  have st4_zh : (run c.R.c6h r4 (zeroHigh s3)).phase = (zeroHigh s3).phase ∧
      regValue c.R.T (run c.R.c6h r4 (zeroHigh s3)).basis = (a + b) ^ 2 ∧
      ∀ q, q ∉ c.R.T → (run c.R.c6h r4 (zeroHigh s3)).basis q = (zeroHigh s3).basis q := by
    as_aux_lemma =>
      have hn6 : (c.R.cin :: ((c.R.dlo ++ c.R.zA) ++ c.R.T ++ c.R.carry.take (c.R.T.length - 1))).Nodup :=
        knd nR (fun q => by
          have := c.R.counts q
          clear * - this
          simp only [KRegs.all, List.count_cons, List.count_append] at this ⊢; omega)
      rw [c.R.c6h_run wR hn6 (zeroHigh s3) r4
        (fun q hq => (regValue_zero _ _).mp s3_car_zh q (List.mem_of_mem_take hq))
        s3_cin_zh (c.R.c6c_bits wR (zeroHigh s3).basis a b s3_T_zh s3_dlo_zh)]
      unfold KRegs.c6
      obtain ⟨p, f, val⟩ := addInPlace_correct (c.R.dlo ++ c.R.zA) c.R.T
        (c.R.carry.take (c.R.T.length - 1)) c.R.cin hn6
        (by rw [List.length_append, L2, L6]; omega)
        (by rw [List.length_take]; omega)
        (zeroHigh s3) r4 (fun q hq => (regValue_zero _ _).mp s3_car_zh q (List.mem_of_mem_take hq))
      refine ⟨p, ?_, f⟩
      rw [val, regValue_append, s3_dlo_zh, s3_zA_zh, s3_T_zh, s3_cin_zh]
      simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false]
      rw [Nat.mod_eq_of_lt (by linarith only [ex, sqLt]), ex]; ring
  have loc4 := run_below20000 c.R.c6h sup_parts.2.2.2.1 s3 r4
  generalize hs4 : run c.R.c6h r4 s3 = s4 at loc4 ⊢
  have s4_F (q : Wire) (hT' : q ∉ c.T) : s4.basis q = s3.basis q := by
    as_aux_lemma =>
      by_cases hq : q < 20000
      · rw [loc4.2 q hq, st4_zh.2.2 q hT']; simp [zeroHigh, Nat.not_le.mpr hq]
      · rw [← hs4]; exact run_ge20000 c.R.c6h sup_parts.2.2.2.1 s3 r4 q (Nat.le_of_not_lt hq)
  have s4_T : regValue c.T s4.basis = (a + b) ^ 2 :=
    (regValue_congr _ _ _ (fun q hq => loc4.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st4_zh.2.1
  have s4_out (q : Wire) (hd : q ∉ c.dst) (hS : q ∉ c.S) (hT' : q ∉ c.T) : s4.basis q = s.basis q :=
    (s4_F q hT').trans ((s3_F q hT').trans ((s2_F q hS).trans (s1_F q hd)))
  have s4_S : regValue c.S s4.basis = a + b :=
    (regValue_congr _ _ s2.basis (fun q hq =>
      (s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))).trans s2_S
  have s4_Q5_bank : regValue c.Q5.bank s4.basis = a + b := by
    as_aux_lemma =>
      by_cases hn : c.n = 128
      · simp only [SplitCfg.Q5, hn, if_true]
        rw [regValue_snoc_zero _ _ _ ((s4_out c.zpad
          (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzpad0), s4_S]
      · simpa [SplitCfg.Q5, hn] using s4_S
  have s4_Q5_dst : regValue c.Q5.dst s4.basis = (regValue c.Q5.bank s4.basis) ^ 2 := by
    as_aux_lemma =>
      rw [s4_Q5_bank]
      by_cases hn : c.n = 128
      · simp only [SplitCfg.Q5, hn, if_true, regValue_append, s4_T]
        have b0 : s4.basis c.zdst0 = false := (s4_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0
        have b1 : s4.basis c.zdst1 = false := (s4_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1
        simp [regValue, b0, b1]
      · simpa [SplitCfg.Q5, hn] using s4_T
  have s4_car0 : regValue c.carry s4.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s4_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s4_pad0 : regValue K0.leafPad s4.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s4_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hpad0 q hq))
  have s4_cin0 : s4.basis K0.core.cin = false :=
    (s4_out _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s4_T5 : regValue c.T5 s4.basis = 2 * ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) :=
    (regValue_congr _ _ s.basis (fun q hq => s4_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT5
  have st5 := DI4Leaves.clear_clean c.Q5 (c.n=128) w5.1 w5.2.1 (Or.inr w5.2.2) n5 s4 r5 (q5_pad_dims c v) (by intro hp; rw [s4_Q5_bank]; have hbb : b<2^64 := (by simpa only [hp] using bLt); norm_num at aLt hbb ⊢; omega) s4_Q5_dst
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by
      rw [c.Q5.lo_mod w5.1, c.Q5.hi_div w5.1, s4_Q5_bank, w5.2.2]
      by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s4_T5)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s4_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s4_cin0)
  generalize hs5 : run (DI4Leaves.clear c.Q5 (c.n=128)) r5 s4 = s5 at st5 ⊢
  have s5_T0 : regValue c.T s5.basis = 0 := by
    as_aux_lemma =>
      have h := st5.2.1
      by_cases hn : c.n = 128
      · simp only [SplitCfg.Q5, hn, if_true, regValue_append] at h; omega
      · simpa [SplitCfg.Q5, hn] using h
  have s5_T5_0 : regValue c.T5 s5.basis = 0 := by as_aux_lemma => by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using st5.2.2.1
  have s5_zd0 : s5.basis c.zdst0 = false ∧ s5.basis c.zdst1 = false := by
    as_aux_lemma =>
      by_cases hn : c.n = 128
      · have h := st5.2.1; simp only [SplitCfg.Q5, hn, if_true] at h
        exact ⟨(regValue_zero _ _).mp h c.zdst0 (by simp), (regValue_zero _ _).mp h c.zdst1 (by simp)⟩
      · exact ⟨(st5.2.2.2 _ (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
          ((s4_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
          (st5.2.2.2 _ (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
          ((s4_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
  have s5_F (q : Wire) (hT' : q ∉ c.T) (hT5' : q ∉ c.T5) : s5.basis q = s4.basis q := by
    as_aux_lemma =>
      by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
      · rcases hzd with rfl | rfl
        · exact s5_zd0.1.trans ((s4_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
            (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
            (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0).symm
        · exact s5_zd0.2.trans ((s4_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
            (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
            (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1).symm
      · apply st5.2.2.2
        · by_cases hn : c.n = 128
          · simp only [SplitCfg.Q5, hn, if_true, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
            rintro (h | rfl | rfl)
            · exact hT' h
            · exact hzd (Or.inl rfl)
            · exact hzd (Or.inr rfl)
          · simpa [SplitCfg.Q5, hn] using hT'
        · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using hT5'
  have s5_S_zh : regValue c.R.S (zeroHigh s5).basis = regValue c.R.lo (zeroHigh s5).basis + regValue c.R.hi (zeroHigh s5).basis := by
    as_aux_lemma =>
      have eS : regValue c.R.S (zeroHigh s5).basis = a + b :=
        (regValue_congr _ _ s4.basis (fun q hq => by
          change q ∈ c.S at hq
          simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
          exact s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s4_S
      have elo : regValue c.R.lo (zeroHigh s5).basis = a :=
        (regValue_congr _ _ s.basis (fun q hq => by
          simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
          exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))).trans
            (s4_out q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
              (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
              (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))))).trans ha
      have ehi : regValue c.R.hi (zeroHigh s5).basis = b :=
        (regValue_congr _ _ s.basis (fun q hq => by
          simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
          exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))).trans
            (s4_out q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
              (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
              (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))))).trans hb
      rw [eS, elo, ehi]
  have st6_zh := c.R.scl1591_correct wR nR (zeroHigh s5) r6 s5_S_zh
    (mk_zh_z s5 (fun q hq => (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s4_out q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))))
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp s4_car0 q hq)))
    (by
      change (zeroHigh s5).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      exact (s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans s4_cin0)
  have loc6 := run_below20000 c.R.scl1591 sup_parts.2.2.2.2 s5 r6
  generalize hs6 : run c.R.scl1591 r6 s5 = s6 at loc6 ⊢
  have s6_F (q : Wire) (hS : q ∉ c.S) : s6.basis q = s5.basis q := by
    as_aux_lemma =>
      by_cases hq : q < 20000
      · rw [loc6.2 q hq, st6_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
      · rw [← hs6]; exact run_ge20000 c.R.scl1591 sup_parts.2.2.2.2 s5 r6 q (Nat.le_of_not_lt hq)
  have s6_S0 : regValue c.S s6.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => loc6.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st6_zh.2.1
  have s6_out (q : Wire) (hd : q ∉ c.dst) (hT' : q ∉ c.T) (hT5' : q ∉ c.T5) : s6.basis q = s.basis q := by
    as_aux_lemma =>
      by_cases hS : q ∈ c.S
      · exact ((regValue_zero _ _).mp s6_S0 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
      · exact (s6_F q hS).trans ((s5_F q hT' hT5').trans (s4_out q hd hS hT'))
  have s6_Q2_bank : regValue c.Q2.bank s6.basis = b := by
    as_aux_lemma =>
      by_cases hn : c.n = 128
      · simp only [SplitCfg.Q2, hn, if_true]
        exact (regValue_congr _ _ s.basis (fun q hq => s6_out q
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
      · simp only [SplitCfg.Q2, hn, if_false]
        rw [regValue_snoc_zero _ _ _ ((s6_out c.zpad
          (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzpad0)]
        exact (regValue_congr _ _ s.basis (fun q hq => s6_out q
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
  have s6_dhi : regValue c.R.dhi s6.basis = b ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq =>
      (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
        (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))))))).trans s1_dhi
  have s6_Q2_dst : regValue c.Q2.dst s6.basis = (regValue c.Q2.bank s6.basis) ^ 2 := by
    as_aux_lemma =>
      rw [s6_Q2_bank]
      by_cases hn : c.n = 128
      · simpa [SplitCfg.Q2, hn] using s6_dhi
      · simp only [SplitCfg.Q2, hn, if_false, regValue_append, s6_dhi]
        have b0 : s6.basis c.zdst0 = false := (s6_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0
        have b1 : s6.basis c.zdst1 = false := (s6_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1
        simp [regValue, b0, b1]
  have s6_car0 : regValue c.carry s6.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s6_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s6_pad0 : regValue K0.leafPad s6.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s6_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hpad0 q hq))
  have s6_cin0 : s6.basis K0.core.cin = false :=
    (s6_out _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s6_T2 : regValue c.T2 s6.basis = 2 * (b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h) :=
    (regValue_congr _ _ s.basis (fun q hq => s6_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT2
  have st7 := DI4Leaves.clear_clean c.Q2 (c.n=129) w2.1 w2.2.1 w2.2.2 n2 s6 r7 (q2_pad_dims c v) (by intro hp; rw [s6_Q2_bank]; simpa only [hp] using bLt) s6_Q2_dst
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by
      rw [c.Q2.lo_mod w2.1, c.Q2.hi_div w2.1, s6_Q2_bank]
      by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s6_T2)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s6_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s6_cin0)
  generalize hs7 : run (DI4Leaves.clear c.Q2 (c.n=129)) r7 s6 = s7 at st7 ⊢
  have s7_dhi0 : regValue c.R.dhi s7.basis = 0 := by
    as_aux_lemma =>
      have h := st7.2.1
      by_cases hn : c.n = 128
      · simpa [SplitCfg.Q2, hn] using h
      · simp only [SplitCfg.Q2, hn, if_false, regValue_append] at h; omega
  have s7_T2_0 : regValue c.T2 s7.basis = 0 := by as_aux_lemma => by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using st7.2.2.1
  have s7_zd0 : s7.basis c.zdst0 = false ∧ s7.basis c.zdst1 = false := by
    as_aux_lemma =>
      by_cases hn : c.n = 128
      · exact ⟨(st7.2.2.2 _ (by simp [SplitCfg.Q2, hn]; exact fun h => dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp) (mDhi h))
          (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
          ((s6_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
          (st7.2.2.2 _ (by simp [SplitCfg.Q2, hn]; exact fun h => dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp) (mDhi h))
          (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
          ((s6_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
      · have h := st7.2.1; simp only [SplitCfg.Q2, hn, if_false] at h
        exact ⟨(regValue_zero _ _).mp h c.zdst0 (by simp), (regValue_zero _ _).mp h c.zdst1 (by simp)⟩
  have s7_F (q : Wire) (hd : q ∉ c.R.dhi) (hT2' : q ∉ c.T2) : s7.basis q = s6.basis q := by
    as_aux_lemma =>
      by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
      · rcases hzd with rfl | rfl
        · exact s7_zd0.1.trans ((s6_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
            (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
            (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0).symm
        · exact s7_zd0.2.trans ((s6_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
            (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
            (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1).symm
      · apply st7.2.2.2
        · by_cases hn : c.n = 128
          · simpa [SplitCfg.Q2, hn] using hd
          · simp only [SplitCfg.Q2, hn, if_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
            rintro (h | rfl | rfl)
            · exact hd h
            · exact hzd (Or.inl rfl)
            · exact hzd (Or.inr rfl)
        · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using hT2'
  have dlo_dhi : ∀ q ∈ c.R.dlo, q ∉ c.R.dhi := by
    as_aux_lemma =>
      intro q h1 h2
      have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
      rw [← List.take_append_drop 128 c.dst] at hnd
      exact (List.nodup_append.mp hnd).2.2 q h1 q h2 rfl
  have s7_dlo : regValue c.R.dlo s7.basis = a ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq =>
      (s7_F q (dlo_dhi q hq) (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))))))))).trans s1_dlo
  have s7_out (q : Wire) (hd : q ∉ c.dst) (hT' : q ∉ c.T) (hT2' : q ∉ c.T2) (hT5' : q ∉ c.T5) : s7.basis q = s.basis q :=
    (s7_F q (fun h => hd (mDhi h)) hT2').trans (s6_out q hd hT' hT5')
  have s7_lo : regValue c.Q1.bank s7.basis = a :=
    (regValue_congr _ _ s.basis (fun q hq => s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
  have s7_T1 : regValue c.T1 s7.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) :=
    (regValue_congr _ _ s.basis (fun q hq => s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT1
  have s7_car0 : regValue c.carry s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s7_pad0 : regValue K0.leafPad s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hpad0 q hq))
  have s7_cin0 : s7.basis K0.core.cin = false :=
    (s7_out _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have st8 := clearC_clean c.Q1 w1.1 w1.2 (Or.inl rfl) n1 s7 r8 (by rw [s7_lo]; exact s7_dlo)
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp s7_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by rw [c.Q1.lo_mod w1.1, c.Q1.hi_div w1.1, s7_lo]; exact s7_T1)
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp s7_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    s7_pad0
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp s7_car0 q (List.mem_of_mem_take h)))
    s7_cin0
  generalize hs8 : run (DI4Square.clearC c.Q1) r8 s7 = s8 at st8 ⊢
  have s8_F (q : Wire) (hd : q ∉ c.R.dlo) (hT1' : q ∉ c.T1) : s8.basis q = s7.basis q := st8.2.2.2 q hd hT1'
  refine ⟨st8.1.trans (st7.1.trans (loc6.1.trans (st6_zh.1.trans (st5.1.trans (loc4.1.trans (st4_zh.1.trans (loc3.1.trans (st3_zh.1.trans (loc2.1.trans (st2_zh.1.trans p1)))))))))),
    ?_, ?_, ?_⟩
  · have h128 := regValue_append c.R.dlo c.R.dhi s8.basis
    rw [show c.R.dlo ++ c.R.dhi = c.dst from List.take_append_drop 128 c.dst] at h128
    have hdhi : regValue c.R.dhi s8.basis = 0 :=
      (regValue_congr _ _ s7.basis (fun q hq => s8_F q (fun h => dlo_dhi q h hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))).trans s7_dhi0
    rw [h128, show c.R.dlo = c.Q1.dst from rfl, st8.2.1, hdhi]; simp
  · have hT_z : regValue c.T s8.basis = 0 :=
      (regValue_congr _ _ s5.basis (fun q hq =>
        (s8_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq (mDlo h))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s7_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq (mDhi h))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
          (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))))).trans s5_T0
    have hT2_z : regValue c.T2 s8.basis = 0 :=
      (regValue_congr _ _ s7.basis (fun q hq => s8_F q
        (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo h) hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s7_T2_0
    have hT5_z : regValue c.T5 s8.basis = 0 :=
      (regValue_congr _ _ s5.basis (fun q hq =>
        (s8_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo h) hq)
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s7_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi h) hq)
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
          (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))))).trans s5_T5_0
    simp only [SplitCfg.liveT, regValue_append, hT_z, show c.T1 = c.Q1.T from rfl, st8.2.2.1, hT2_z, hT5_z]
    simp
  · intro q hd hL
    have hT' : q ∉ c.T := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT1' : q ∉ c.T1 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT2' : q ∉ c.T2 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT5' : q ∉ c.T5 := fun h => hL (by simp [SplitCfg.liveT, h])
    exact (s8_F q (fun h => hd (mDlo h)) hT1').trans (s7_out q hd hT' hT2' hT5')

theorem cfg_counts_H (c : SplitCfg) (v : CfgValid c) (hn : c.n = 128) (src dst : List Wire)
    (hs : src.length = 128) (hd : dst.length = 256) :
    let oldK := LowZero18LowK.kg K0 E0 src dst
    toffoliCount c.makeRef + toffoliCount c.clearRef + 374 =
      toffoliCount (LowZero18Square.make K0 oldK) + toffoliCount (LowZero18Square.clear K0 oldK) ∧
    measurementCount c.makeRef + measurementCount c.clearRef + 197 =
      measurementCount (LowZero18Square.make K0 oldK) + measurementCount (LowZero18Square.clear K0 oldK) := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  have wOld := LowZero18LowK.oregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wiOld := LowZero18LowK.iregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wjOld := LowZero18LowK.jregsH_W K0 hwK E0 src dst hs (by omega) hext.len
  have m8_R8 := c.R8.m8z_counts wR8; have c8_R8 := c.R8.c8z_counts wR8
  have m8_R := c.R.m8z_counts wR; have c8_R := c.R.c8z_counts wR
  have bR : c.R.bank.length = 128 := by simp [SplitCfg.R, v.bankLen, hn]
  have bOld : (LowZero18LowK.oregs K0 E0 src dst).bank.length = 128 := by
    simp [LowZero18LowK.oregs, (K0.measured_bank_widths hwK).1, hs]
  have hOldH : (LowZero18LowK.oregs K0 E0 src dst).h = 64 := rfl
  have biOld : (LowZero18LowK.iregs K0 E0 src dst).bank.length = 64 := by
    simp [LowZero18LowK.iregs, KRegs.lo, bOld, hOldH]
  have bjOld : (LowZero18LowK.jregsH K0 E0 src dst).bank.length = 64 := by
    simp [LowZero18LowK.jregsH, KRegs.hi, bOld, hOldH]
  have oldEq : LowZero18LowK.kg K0 E0 src dst = LowZero18LowK.kgH K0 E0 src dst := by simp [LowZero18LowK.kg, hs]
  have om := LowZero18KG.make_counts (LowZero18LowK.kgH K0 E0 src dst) wOld
  have oc := LowZero18KG.clear_counts (LowZero18LowK.kgH K0 E0 src dst) wOld
  have pm := LowZero18Square.patchKG_counts K0 (LowZero18LowK.kg K0 E0 src dst)
  let K :=
    { LowZero18LowK.kgH K0 E0 src dst with
      R := c.R, X1 := [], X2 := [], X5 := [],
      Q1 := LowZero18Diagonal.makeC c.Q1, Q1c := LowZero18Diagonal.clearC c.Q1,
      Q2 := LowZero18Diagonal.makeC c.Q2, Q2c := LowZero18Diagonal.clearC c.Q2,
      Q5 := LowZero18Diagonal.makeC c.Q5, Q5c := LowZero18Diagonal.clearC c.Q5,
      I1 := fun _ _ => True, I2 := fun _ _ => True, I5 := fun _ _ => True }
  have nm := LowZero18KG.make_counts K wR
  have nc := LowZero18KG.clear_counts K wR
  have m8z_eq : toffoliCount c.R8.m8z = toffoliCount c.R.m8z ∧ measurementCount c.R8.m8z = measurementCount c.R.m8z ∧
      toffoliCount c.R8.c8z = toffoliCount c.R.c8z ∧ measurementCount c.R8.c8z = measurementCount c.R.c8z := by
    have lR := c.R.m8z_lens wR; have lR8 := c.R8.m8z_lens wR8
    have hd8 : c.R8.dmid.length = c.R.dmid.length := by simp [KRegs.dmid, SplitCfg.R8, SplitCfg.R]
    have a1 := addInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have a2 := addInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have s1 := subInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have s2 := subInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have m8t : toffoliCount c.R8.m8 = toffoliCount c.R.m8 := by simp only [KRegs.m8, a1.1, a2.1]; rw [hd8]
    have m8m : measurementCount c.R8.m8 = measurementCount c.R.m8 := by simp only [KRegs.m8, a1.2, a2.2]; rw [hd8]
    have c8t : toffoliCount c.R8.c8 = toffoliCount c.R.c8 := by simp only [KRegs.c8, s1.1, s2.1]; rw [hd8]
    have c8m : measurementCount c.R8.c8 = measurementCount c.R.c8 := by simp only [KRegs.c8, s1.2, s2.2]; rw [hd8]
    exact ⟨by linarith only [m8_R8.1, m8_R.1, m8t], by linarith only [m8_R8.2, m8_R.2, m8m],
      by linarith only [c8_R8.1, c8_R.1, c8t], by linarith only [c8_R8.2, c8_R.2, c8m]⟩
  have hNewM : toffoliCount c.makeRef = toffoliCount (LowZero18KG.make K) ∧
      measurementCount c.makeRef = measurementCount (LowZero18KG.make K) := by
    simp only [SplitCfg.makeRef, LowZero18KG.make, K, toffoliCount_append, measurementCount_append, m8z_eq.1, m8z_eq.2.1]
    exact ⟨by ring, by ring⟩
  have hNewC : toffoliCount c.clearRef = toffoliCount (LowZero18KG.clear K) ∧
      measurementCount c.clearRef = measurementCount (LowZero18KG.clear K) := by
    simp only [SplitCfg.clearRef, LowZero18KG.clear, K, toffoliCount_append, measurementCount_append, m8z_eq.2.2.1, m8z_eq.2.2.2]
    exact ⟨by ring, by ring⟩
  have c_eq32 (A B : KRegs) (wA : A.W) (wB : B.W) (hA : A.h = 32) (hB : B.h = 32)
      (bA : A.bank.length = 64) (bB : B.bank.length = 64) :
      DiagSq.cost A = DiagSq.cost B ∧ DiagSq.parR A = DiagSq.parR B := by
    have sA : A.S.length = 33 := by have := wA.S; omega
    have sB : B.S.length = 33 := by have := wB.S; omega
    have loA : A.lo.length = 32 := by simp [KRegs.lo, bA, hA]
    have loB : B.lo.length = 32 := by simp [KRegs.lo, bB, hB]
    have hiA : A.hi.length = 32 := by simp [KRegs.hi, bA, hA]
    have hiB : B.hi.length = 32 := by simp [KRegs.hi, bB, hB]
    exact ⟨by simp [DiagSq.cost, bA, bB, hA, hB], by simp [DiagSq.parR, loA, loB, hiA, hiB, sA, sB]⟩
  have eQ1 := c_eq32 c.Q1 (LowZero18LowK.iregs K0 E0 src dst) w1.1 wiOld rfl rfl
    (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]) biOld
  have eQ2 := c_eq32 c.Q2 (LowZero18LowK.jregsH K0 E0 src dst) w2.1 wjOld
    (by simp [SplitCfg.Q2, hn]) rfl (by simp [SplitCfg.Q2, hn, KRegs.hi, SplitCfg.R, v.bankLen]) bjOld
  have q1_m := makeC_counts c.Q1 w1.1 w1.2; have q1_c := RawClearSquare.clear_counts c.Q1 w1.1 w1.2
  have q1_d := diag32_counts c.Q1 w1.1 rfl (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn])
  have qi_m := makeC_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_c := RawClearSquare.clear_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_d := diag32_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld rfl biOld
  have hQ1 : toffoliCount K.Q1 + toffoliCount K.Q1c =
      toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q1 + toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q1c ∧
      measurementCount K.Q1 + measurementCount K.Q1c =
      measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q1 + measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q1c := by
    have b1 : c.Q1.bank.length = 64 := by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]
    have h1 : c.Q1.h = 32 := rfl
    have hi : (LowZero18LowK.iregs K0 E0 src dst).h = 32 := rfl
    have ⟨_, _, q1d3, q1d4⟩ := q1_d
    have ⟨_, _, qid3, qid4⟩ := qi_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q1) = toffoliCount (RawClearSquare.clear c.Q1) + 31 at q1d3
    change measurementCount (LowZero18Diagonal.clearC c.Q1) = measurementCount (RawClearSquare.clear c.Q1) + 32 at q1d4
    change toffoliCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      toffoliCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 31 at qid3
    change measurementCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      measurementCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 32 at qid4
    simp only [K, LowZero18LowK.kgH]
    rw [b1, h1] at q1_m; rw [h1] at q1_c; rw [biOld, hi] at qi_m; rw [hi] at qi_c
    exact ⟨by clear * - q1_m q1_c q1d3 qi_m qi_c qid3 eQ1; omega,
      by clear * - q1_m q1_c q1d4 qi_m qi_c qid4 eQ1; omega⟩
  have q2_m := LowZero18Diagonal.make_counts c.Q2 w2.1 w2.2.1; have q2_c := RawClearSquare.clear_counts c.Q2 w2.1 w2.2.1
  have q2_d := diag32_counts c.Q2 w2.1 (by simp [SplitCfg.Q2, hn]) (by simp [SplitCfg.Q2, hn, KRegs.hi, SplitCfg.R, v.bankLen])
  have qj_m := LowZero18Diagonal.make_counts (LowZero18LowK.jregsH K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have qj_c := RawClearSquare.clear_counts (LowZero18LowK.jregsH K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have hQ2 : toffoliCount K.Q2 + toffoliCount K.Q2c =
      toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q2 + toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q2c + 31 ∧
      measurementCount K.Q2 + measurementCount K.Q2c =
      measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q2 + measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q2c + 64 := by
    have h2 : c.Q2.h = 32 := by simp [SplitCfg.Q2, hn]
    have hj : (LowZero18LowK.jregsH K0 E0 src dst).h = 32 := rfl
    have ⟨q2d1, q2d2, q2d3, q2d4⟩ := q2_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q2) = toffoliCount (RawClearSquare.clear c.Q2) + 31 at q2d3
    change measurementCount (LowZero18Diagonal.clearC c.Q2) = measurementCount (RawClearSquare.clear c.Q2) + 32 at q2d4
    simp only [K, LowZero18LowK.kgH, LowZero18Diagonal.clear]
    rw [h2] at q2_c; rw [hj] at qj_c
    exact ⟨by clear * - q2_m q2_c q2d1 q2d3 qj_m qj_c eQ2; omega,
      by clear * - q2_m q2_c q2d2 q2d4 qj_m qj_c eQ2; omega⟩
  have q5_e := diag33_exact c.Q5 w5.1 w5.2.2 (by rw [w5.2.1, w5.2.2])
  have q5_old := tsq65_exact (LowZero18LowK.oregs K0 E0 src dst).S (LowZero18LowK.oregs K0 E0 src dst).T
    (LowZero18LowK.oregs K0 E0 src dst).pad (LowZero18LowK.oregs K0 E0 src dst).carry
    (LowZero18LowK.oregs K0 E0 src dst).cin
    (by have hOS := wOld.S; rw [bOld, hOldH] at hOS; omega)
    (by have hOT := wOld.T; have hOS := wOld.S; rw [bOld, hOldH] at hOS; omega)
    wOld.pad (by have := wOld.carry; omega)
  have hQ5 : toffoliCount K.Q5 + toffoliCount K.Q5c + 405 =
      toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q5 + toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q5c ∧
      measurementCount K.Q5 + measurementCount K.Q5c + 261 =
      measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q5 + measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q5c := by
    simp only [K, LowZero18LowK.kgH]
    exact ⟨by clear * - q5_e q5_old; omega, by clear * - q5_e q5_old; omega⟩
  have hOldT : toffoliCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.make (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.1, oldEq]
  have hOldM : measurementCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.make (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.2.1, oldEq]
  have hOldCT : toffoliCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.clear (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.2.2.1, oldEq]
  have hOldCM : measurementCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.clear (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.2.2.2, oldEq]
  dsimp only
  rw [hNewM.1, hNewM.2, hNewC.1, hNewC.2, hOldT, hOldM, hOldCT, hOldCM]
  have hKR : K.R = c.R := rfl
  have hOR : (LowZero18LowK.kgH K0 E0 src dst).R = LowZero18LowK.oregs K0 E0 src dst := rfl
  have ht1 : ¬c.R.trimOK := by simp only [KRegs.trimOK, bR, show c.R.h = 64 from rfl]; decide
  have ht2 : ¬(LowZero18LowK.oregs K0 E0 src dst).trimOK := by simp only [KRegs.trimOK, bOld, hOldH]; decide
  rw [hKR] at nm nc; simp only [ht1, if_false] at nm nc; rw [bR, show c.R.h = 64 from rfl] at nm nc
  rw [hOR] at om oc; simp only [ht2, if_false] at om oc; rw [bOld, hOldH] at om oc
  exact ⟨by clear * - nm nc om oc hQ1 hQ2 hQ5; omega,
    by clear * - nm nc om oc hQ1 hQ2 hQ5; omega⟩

theorem cfg_counts_S (c : SplitCfg) (v : CfgValid c) (hn : c.n = 129) (src dst : List Wire)
    (hs : src.length = 129) (hd : dst.length = 258) :
    let oldK := LowZero18LowK.kg K0 E0 src dst
    toffoliCount c.makeRef + toffoliCount c.clearRef + 373 =
      toffoliCount (LowZero18Square.make K0 oldK) + toffoliCount (LowZero18Square.clear K0 oldK) ∧
    measurementCount c.makeRef + measurementCount c.clearRef + 195 =
      measurementCount (LowZero18Square.make K0 oldK) + measurementCount (LowZero18Square.clear K0 oldK) := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  have wOld := LowZero18LowK.oregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wiOld := LowZero18LowK.iregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wjOld := LowZero18LowK.jregsS_W K0 hwK E0 src dst hs (by omega) hext.len
  have m8_R8 := c.R8.m8z_counts wR8; have c8_R8 := c.R8.c8z_counts wR8
  have m8_R := c.R.m8z_counts wR; have c8_R := c.R.c8z_counts wR
  have bR : c.R.bank.length = 129 := by simp [SplitCfg.R, v.bankLen, hn]
  have bOld : (LowZero18LowK.oregs K0 E0 src dst).bank.length = 129 := by
    simp [LowZero18LowK.oregs, (K0.measured_bank_widths hwK).1, hs]
  have hOldH : (LowZero18LowK.oregs K0 E0 src dst).h = 64 := rfl
  have biOld : (LowZero18LowK.iregs K0 E0 src dst).bank.length = 64 := by
    simp [LowZero18LowK.iregs, KRegs.lo, bOld, hOldH]
  have bjOld : (LowZero18LowK.jregsS K0 E0 src dst).bank.length = 66 := by
    have hOS := wOld.S; simp [LowZero18LowK.jregsS, hOS, bOld, hOldH]
  have oldEq : LowZero18LowK.kg K0 E0 src dst = LowZero18LowK.kgS K0 E0 src dst := by simp [LowZero18LowK.kg, hs]
  have om := LowZero18KG.make_counts (LowZero18LowK.kgS K0 E0 src dst) wOld
  have oc := LowZero18KG.clear_counts (LowZero18LowK.kgS K0 E0 src dst) wOld
  have pm := LowZero18Square.patchKG_counts K0 (LowZero18LowK.kg K0 E0 src dst)
  let K :=
    { LowZero18LowK.kgH K0 E0 src dst with
      R := c.R, X1 := [], X2 := [], X5 := [],
      Q1 := LowZero18Diagonal.makeC c.Q1, Q1c := LowZero18Diagonal.clearC c.Q1,
      Q2 := LowZero18Diagonal.makeC c.Q2, Q2c := LowZero18Diagonal.clearC c.Q2,
      Q5 := LowZero18Diagonal.makeC c.Q5, Q5c := LowZero18Diagonal.clearC c.Q5,
      I1 := fun _ _ => True, I2 := fun _ _ => True, I5 := fun _ _ => True }
  have nm := LowZero18KG.make_counts K wR
  have nc := LowZero18KG.clear_counts K wR
  have m8z_eq : toffoliCount c.R8.m8z = toffoliCount c.R.m8z ∧ measurementCount c.R8.m8z = measurementCount c.R.m8z ∧
      toffoliCount c.R8.c8z = toffoliCount c.R.c8z ∧ measurementCount c.R8.c8z = measurementCount c.R.c8z := by
    have lR := c.R.m8z_lens wR; have lR8 := c.R8.m8z_lens wR8
    have hd8 : c.R8.dmid.length = c.R.dmid.length := by simp [KRegs.dmid, SplitCfg.R8, SplitCfg.R]
    have a1 := addInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have a2 := addInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have s1 := subInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have s2 := subInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have m8t : toffoliCount c.R8.m8 = toffoliCount c.R.m8 := by simp only [KRegs.m8, a1.1, a2.1]; rw [hd8]
    have m8m : measurementCount c.R8.m8 = measurementCount c.R.m8 := by simp only [KRegs.m8, a1.2, a2.2]; rw [hd8]
    have c8t : toffoliCount c.R8.c8 = toffoliCount c.R.c8 := by simp only [KRegs.c8, s1.1, s2.1]; rw [hd8]
    have c8m : measurementCount c.R8.c8 = measurementCount c.R.c8 := by simp only [KRegs.c8, s1.2, s2.2]; rw [hd8]
    exact ⟨by linarith only [m8_R8.1, m8_R.1, m8t], by linarith only [m8_R8.2, m8_R.2, m8m],
      by linarith only [c8_R8.1, c8_R.1, c8t], by linarith only [c8_R8.2, c8_R.2, c8m]⟩
  have hNewM : toffoliCount c.makeRef = toffoliCount (LowZero18KG.make K) ∧
      measurementCount c.makeRef = measurementCount (LowZero18KG.make K) := by
    simp only [SplitCfg.makeRef, LowZero18KG.make, K, toffoliCount_append, measurementCount_append, m8z_eq.1, m8z_eq.2.1]
    exact ⟨by ring, by ring⟩
  have hNewC : toffoliCount c.clearRef = toffoliCount (LowZero18KG.clear K) ∧
      measurementCount c.clearRef = measurementCount (LowZero18KG.clear K) := by
    simp only [SplitCfg.clearRef, LowZero18KG.clear, K, toffoliCount_append, measurementCount_append, m8z_eq.2.2.1, m8z_eq.2.2.2]
    exact ⟨by ring, by ring⟩
  have hne : c.n ≠ 128 := by omega
  have c_eq (A B : KRegs) (wA : A.W) (wB : B.W) (h : Nat) (hA : A.h = h) (hB : B.h = h)
      (bA : A.bank.length = 2 * h) (bB : B.bank.length = 2 * h) :
      DiagSq.cost A = DiagSq.cost B ∧ DiagSq.parR A = DiagSq.parR B := by
    have sA : A.S.length = h + 1 := by have := wA.S; omega
    have sB : B.S.length = h + 1 := by have := wB.S; omega
    have loA : A.lo.length = h := by simp [KRegs.lo, bA, hA]; omega
    have loB : B.lo.length = h := by simp [KRegs.lo, bB, hB]; omega
    have hiA : A.hi.length = h := by simp [KRegs.hi, bA, hA]; omega
    have hiB : B.hi.length = h := by simp [KRegs.hi, bB, hB]; omega
    exact ⟨by simp [DiagSq.cost, bA, bB, hA, hB], by simp [DiagSq.parR, loA, loB, hiA, hiB, sA, sB]⟩
  have eQ1 := c_eq c.Q1 (LowZero18LowK.iregs K0 E0 src dst) w1.1 wiOld 32 rfl rfl
    (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]) biOld
  have eQ5 := c_eq c.Q5 (LowZero18LowK.jregsS K0 E0 src dst) w5.1 wjOld 33 w5.2.2 rfl
    (by rw [w5.2.1, w5.2.2]) bjOld
  have q1_m := makeC_counts c.Q1 w1.1 w1.2; have q1_c := RawClearSquare.clear_counts c.Q1 w1.1 w1.2
  have q1_d := diag32_counts c.Q1 w1.1 rfl (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn])
  have qi_m := makeC_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_c := RawClearSquare.clear_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_d := diag32_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld rfl biOld
  have hQ1 : toffoliCount K.Q1 + toffoliCount K.Q1c =
      toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q1 + toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q1c ∧
      measurementCount K.Q1 + measurementCount K.Q1c =
      measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q1 + measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q1c := by
    have b1 : c.Q1.bank.length = 64 := by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]
    have h1 : c.Q1.h = 32 := rfl
    have hi : (LowZero18LowK.iregs K0 E0 src dst).h = 32 := rfl
    have ⟨_, _, q1d3, q1d4⟩ := q1_d
    have ⟨_, _, qid3, qid4⟩ := qi_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q1) = toffoliCount (RawClearSquare.clear c.Q1) + 31 at q1d3
    change measurementCount (LowZero18Diagonal.clearC c.Q1) = measurementCount (RawClearSquare.clear c.Q1) + 32 at q1d4
    change toffoliCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      toffoliCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 31 at qid3
    change measurementCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      measurementCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 32 at qid4
    simp only [K, LowZero18LowK.kgS]
    rw [b1, h1] at q1_m; rw [h1] at q1_c; rw [biOld, hi] at qi_m; rw [hi] at qi_c
    exact ⟨by clear * - q1_m q1_c q1d3 qi_m qi_c qid3 eQ1; omega,
      by clear * - q1_m q1_c q1d4 qi_m qi_c qid4 eQ1; omega⟩
  have q2_e := diag33_exact c.Q2 w2.1 (by simp [SplitCfg.Q2, hne]) (by simp [SplitCfg.Q2, hne, KRegs.hi, SplitCfg.R, v.bankLen, hn])
  have q2_old := tsq65_exact (LowZero18LowK.oregs K0 E0 src dst).hi (LowZero18LowK.oregs K0 E0 src dst).dhi
    (LowZero18LowK.oregs K0 E0 src dst).pad (LowZero18LowK.oregs K0 E0 src dst).carry
    (LowZero18LowK.oregs K0 E0 src dst).cin
    (by simp [KRegs.hi, bOld, hOldH]) (by simp [KRegs.dhi, LowZero18LowK.oregs, hd, hOldH]) wOld.pad (by have := wOld.carry; omega)
  have hQ2 : toffoliCount K.Q2 + toffoliCount K.Q2c + 405 =
      toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q2 + toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q2c ∧
      measurementCount K.Q2 + measurementCount K.Q2c + 261 =
      measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q2 + measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q2c := by
    simp only [K, LowZero18LowK.kgS]
    exact ⟨by clear * - q2_e q2_old; omega, by clear * - q2_e q2_old; omega⟩
  have q5_m := LowZero18Diagonal.make_counts c.Q5 w5.1 w5.2.1; have q5_c := RawClearSquare.clear_counts c.Q5 w5.1 w5.2.1
  have q5_d := diag33_counts c.Q5 w5.1 w5.2.2 (by rw [w5.2.1, w5.2.2])
  have qj_m := LowZero18Diagonal.make_counts (LowZero18LowK.jregsS K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have qj_c := RawClearSquare.clear_counts (LowZero18LowK.jregsS K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have hQ5 : toffoliCount K.Q5 + toffoliCount K.Q5c =
      toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q5 + toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q5c + 32 ∧
      measurementCount K.Q5 + measurementCount K.Q5c =
      measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q5 + measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q5c + 66 := by
    have h5 : c.Q5.h = 33 := w5.2.2
    have hj : (LowZero18LowK.jregsS K0 E0 src dst).h = 33 := rfl
    have ⟨q5d1, q5d2, q5d3, q5d4⟩ := q5_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q5) = toffoliCount (RawClearSquare.clear c.Q5) + 32 at q5d3
    change measurementCount (LowZero18Diagonal.clearC c.Q5) = measurementCount (RawClearSquare.clear c.Q5) + 33 at q5d4
    simp only [K, LowZero18LowK.kgS, LowZero18Diagonal.clear]
    rw [h5] at q5_c; rw [hj] at qj_c
    exact ⟨by clear * - q5_m q5_c q5d1 q5d3 qj_m qj_c eQ5; omega,
      by clear * - q5_m q5_c q5d2 q5d4 qj_m qj_c eQ5; omega⟩
  have hOldT : toffoliCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.make (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.1, oldEq]
  have hOldM : measurementCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.make (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.2.1, oldEq]
  have hOldCT : toffoliCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.clear (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.2.2.1, oldEq]
  have hOldCM : measurementCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.clear (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.2.2.2, oldEq]
  dsimp only
  rw [hNewM.1, hNewM.2, hNewC.1, hNewC.2, hOldT, hOldM, hOldCT, hOldCM]
  have hKR : K.R = c.R := rfl
  have hOR : (LowZero18LowK.kgS K0 E0 src dst).R = LowZero18LowK.oregs K0 E0 src dst := rfl
  have ht1 : c.R.trimOK := by simp only [KRegs.trimOK, bR, show c.R.h = 64 from rfl]; decide
  have ht2 : (LowZero18LowK.oregs K0 E0 src dst).trimOK := by simp only [KRegs.trimOK, bOld, hOldH]; decide
  rw [hKR] at nm nc; simp only [ht1, if_true] at nm nc; rw [bR, show c.R.h = 64 from rfl] at nm nc
  rw [hOR] at om oc; simp only [ht2, if_true] at om oc; rw [bOld, hOldH] at om oc
  exact ⟨by clear * - nm nc om oc hQ1 hQ2 hQ5; omega,
    by clear * - nm nc om oc hQ1 hQ2 hQ5; omega⟩

end SplitCore

/-! ### Slot bounds for the concrete split Karatsuba kernels -/

section SplitSlots
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

private theorem addInPlace_slots_eq : ∀ (x y cs : List Wire) (c : Wire),
    x.length = y.length → x.length - 1 ≤ cs.length → 1 ≤ x.length →
    Challenge.gateSlots (addInPlace x y cs c) = 12 * x.length - 10
  | [a], [b], _, c, _, _, _ => by
      simp [addInPlace, Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots]
  | a :: a' :: as, b :: b' :: bs, d :: ds, c, hxy, hcs, _ => by
      simp only [List.length_cons] at hxy hcs
      have ih := addInPlace_slots_eq (a' :: as) (b' :: bs) ds d
        (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega) (by simp)
      simp only [addInPlace, Challenge.gateSlots_append, Baselines.majority_gateSlots,
        Baselines.eraseCarry_gateSlots, Baselines.gateSlots_cons, Baselines.gateSlots_nil,
        Challenge.instructionSlots, List.length_cons] at ih ⊢
      omega
  | [], _, _, _, _, _, hx => by simp at hx
  | [_], [], _, _, hxy, _, _ => by simp at hxy
  | [_], _ :: _ :: _, _, _, hxy, _, _ => by simp at hxy
  | _ :: _ :: _, [], _, _, hxy, _, _ => by simp at hxy
  | _ :: _ :: _, [_], _, _, hxy, _, _ => by simp at hxy
  | _ :: _ :: _, _ :: _ :: _, [], _, _, hcs, _ => by simp at hcs

private theorem m8z_slots_eq (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.m8z = 12 * (R.dmid.length - 1) - 9 := by
  have l := R.m8z_lens w
  have h1 := l.1; have h2 := l.2.1; have h3 := l.2.2
  have ha := addInPlace_slots_eq (R.T ++ R.zM).tail R.dmid.tail (R.carry.take (R.dmid.length - 1)).tail R.cin
    (by simp only [List.length_tail, h1])
    (by simp only [List.length_tail, h1]; omega)
    (by simp only [List.length_tail, h1]; omega)
  simp only [KRegs.m8z, LowZero.addLow0, Challenge.gateSlots_append, ha, List.length_tail, h1,
    Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, List.length_nil]
  omega

private theorem c8z_slots_eq (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.c8z = 2 * R.dmid.length + 12 * (R.dmid.length - 1) - 7 := by
  have l := R.m8z_lens w
  have h1 := l.1; have h2 := l.2.1; have h3 := l.2.2
  have ha := addInPlace_slots_eq (R.T ++ R.zM).tail R.dmid.tail (R.carry.take (R.dmid.length - 1)).tail R.cin
    (by simp only [List.length_tail, h1])
    (by simp only [List.length_tail, h1]; omega)
    (by simp only [List.length_tail, h1]; omega)
  simp only [KRegs.c8z, LowZero.subLowNC, LowZero.addLowNC, Challenge.gateSlots_append, ha,
    Baselines.notRegister_gateSlots, List.length_tail, h1,
    Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, List.length_nil]
  omega

private theorem diagC_slots_bound (R : KRegs) (w : R.W) (he : R.bank.length = 2 * R.h) (hh : R.h ≤ 33) :
    Challenge.gateSlots (LowZero18Diagonal.makeC R) + Challenge.gateSlots (LowZero18Diagonal.clearC R) ≤ 601600 := by
  have dt := LowZero18Diagonal.tiny_slots R w he hh
  have ot := R.tiny_slots w hh (by omega) (by omega)
  have ms := R.make_sub_slots w
  have sc := R.scl1591_slots
  have sk := R.smkT_slots
  simp only [LowZero18Diagonal.makeC, LowZero18Diagonal.clearC, RawClearSquare.clearC, LowZero18Diagonal.clear,
    Challenge.gateSlots_append] at dt ⊢
  clear * - dt ot ms sc sk; omega

theorem cfg_slots_bound_ref (c : SplitCfg) (v : CfgValid c) :
    Challenge.gateSlots c.makeRef + Challenge.gateSlots c.clearRef ≤ 1830000 := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  have q1 := diagC_slots_bound c.Q1 w1.1 w1.2 (by change 32 ≤ 33; decide)
  have q2 := diagC_slots_bound c.Q2 w2.1 w2.2.1 (by rcases w2.2.2 with h | h <;> omega)
  have q5 := diagC_slots_bound c.Q5 w5.1 w5.2.1 (by omega)
  have m8 := m8z_slots_eq c.R wR; have m8' := m8z_slots_eq c.R8 wR8
  have c8 := c8z_slots_eq c.R wR; have c8' := c8z_slots_eq c.R8 wR8
  have hd8 : c.R8.dmid.length = c.R.dmid.length := by simp [KRegs.dmid, SplitCfg.R8, SplitCfg.R]
  have ad := c.R.adder_slots wR rfl (by simp only [SplitCfg.R, v.bankLen]; rcases v.hn with h | h <;> omega)
  let K :=
    { LowZero18LowK.kgH K0 E0 c.src c.dst with
      R := c.R, X1 := [], X2 := [], X5 := [],
      Q1 := LowZero18Diagonal.makeC c.Q1, Q1c := LowZero18Diagonal.clearC c.Q1,
      Q2 := LowZero18Diagonal.makeC c.Q2, Q2c := LowZero18Diagonal.clearC c.Q2,
      Q5 := LowZero18Diagonal.makeC c.Q5, Q5c := LowZero18Diagonal.clearC c.Q5,
      I1 := fun _ _ => True, I2 := fun _ _ => True, I5 := fun _ _ => True }
  have st := LowZero18KG.steps_slots2 K wR
  have hM : Challenge.gateSlots c.makeRef = Challenge.gateSlots (LowZero18KG.make K) := by
    simp only [SplitCfg.makeRef, LowZero18KG.make, K, Challenge.gateSlots_append, m8, m8', hd8]; ring
  have hC : Challenge.gateSlots c.clearRef = Challenge.gateSlots (LowZero18KG.clear K) := by
    simp only [SplitCfg.clearRef, LowZero18KG.clear, K, Challenge.gateSlots_append, c8, c8', hd8]; ring
  rw [hM, hC]
  dsimp only [K] at st ⊢
  clear * - q1 q2 q5 ad st; omega


theorem clearC_measurements (Q : KRegs) :
    measurementCount (DI4Square.clearC Q)=measurementCount (LowZero18Diagonal.clearC Q) := by
  simp only [DI4Square.clearC,LowZero18Diagonal.clearC,RawClearSquare.clearC,measurementCount_append,
    (DI4Square.clear_resources Q).2.2.1]

theorem clearC_slots (Q : KRegs) :
    Challenge.gateSlots (DI4Square.clearC Q)≤Challenge.gateSlots (LowZero18Diagonal.clearC Q) := by
  have h := (DI4Square.clear_resources Q).2.2.2
  simp only [DI4Square.clearC,LowZero18Diagonal.clearC,RawClearSquare.clearC,Challenge.gateSlots_append]
  omega

theorem cfg_clear_measurements (c : SplitCfg) (v : CfgValid c) :
    measurementCount c.clear=measurementCount c.clearRef := by
  have cm := (DI4Merge.safe_resources c.R8).2.2.1
  rw [DI4Merge.c8g_eq_c8z c.R8 (cfg_R8_W c v)] at cm
  have q2 := DI4Leaves.clear_measurements c.Q2 (c.n=129) (cfg_Q2_W c v).1
  have q5 := DI4Leaves.clear_measurements c.Q5 (c.n=128) (cfg_Q5_W c v).1
  simp only [SplitCfg.clear,SplitCfg.clearRef,measurementCount_append,clearC_measurements,cm,q2,q5]

theorem cfg_make_measurements (c : SplitCfg) (v : CfgValid c) :
    measurementCount c.make=measurementCount c.makeRef := by
  have q2 := DI4Leaves.make_measurements c.Q2 (c.n=129) (cfg_Q2_W c v).1
  have q5 := DI4Leaves.make_measurements c.Q5 (c.n=128) (cfg_Q5_W c v).1
  simp only [SplitCfg.make,SplitCfg.makeRef,measurementCount_append,q2,q5]

theorem cfg_slots_bound (c : SplitCfg) (v : CfgValid c) :
    Challenge.gateSlots c.make + Challenge.gateSlots c.clear ≤ 1830000 := by
  have old := cfg_slots_bound_ref c v
  have cm := (DI4Merge.safe_resources c.R8).2.2.2
  rw [DI4Merge.c8g_eq_c8z c.R8 (cfg_R8_W c v)] at cm
  have m2 := DI4Leaves.make_slots c.Q2 (c.n=129) (cfg_Q2_W c v).1
  have m5 := DI4Leaves.make_slots c.Q5 (c.n=128) (cfg_Q5_W c v).1
  have c1 := clearC_slots c.Q1
  have c2 := DI4Leaves.clear_slots c.Q2 (c.n=129) (cfg_Q2_W c v).1
  have c5 := DI4Leaves.clear_slots c.Q5 (c.n=128) (cfg_Q5_W c v).1
  simp only [SplitCfg.make,SplitCfg.makeRef,SplitCfg.clear,SplitCfg.clearRef,Challenge.gateSlots_append] at old ⊢
  omega

theorem c7fast_cfgA_Q1_geometry : DI4C7Fast.Geometry cfgA.Q1 := by
  simp only [cfgA_fast,SplitCfg.Q1_fast]
  decide +kernel

theorem c7fast_cfgA_Q1_active : DI4LastCarry.Active cfgA.Q1 :=
  DI4C7Fast.active_of_geometry cfgA.Q1 (cfg_Q1_W cfgA cfgA_valid).1
    (cfg_nodups cfgA cfgA_valid).2.2.1 c7fast_cfgA_Q1_geometry

theorem cfgA_Q1_c7_active : DI4LastCarry.Active cfgA.Q1 := c7fast_cfgA_Q1_active

theorem c7fast_cfgA_Q2_geometry : DI4C7Fast.Geometry cfgA.Q2 := by
  simp only [cfgA_fast,SplitCfg.Q2_fast]
  decide +kernel

theorem c7fast_cfgA_Q2_active : DI4LastCarry.Active cfgA.Q2 :=
  DI4C7Fast.active_of_geometry cfgA.Q2 (cfg_Q2_W cfgA cfgA_valid).1
    (cfg_nodups cfgA cfgA_valid).2.2.2.1 c7fast_cfgA_Q2_geometry

theorem cfgA_Q2_c7_active : DI4LastCarry.Active cfgA.Q2 := c7fast_cfgA_Q2_active

theorem c7fast_cfgA_Q5_geometry : DI4C7Fast.Geometry cfgA.Q5 := by
  simp only [cfgA_fast,SplitCfg.Q5_fast]
  decide +kernel

theorem c7fast_cfgA_Q5_active : DI4LastCarry.Active cfgA.Q5 :=
  DI4C7Fast.active_of_geometry cfgA.Q5 (cfg_Q5_W cfgA cfgA_valid).1
    (cfg_nodups cfgA cfgA_valid).2.2.2.2 c7fast_cfgA_Q5_geometry

theorem cfgA_Q5_c7_active : DI4LastCarry.Active cfgA.Q5 := c7fast_cfgA_Q5_active

theorem cfgA_Q1_merge_active : DI4Merge.Active cfgA.Q1 :=
  DI4Merge.active_of_W cfgA.Q1 (cfg_Q1_W cfgA cfgA_valid).1 (cfg_nodups cfgA cfgA_valid).2.2.1

theorem cfgA_Q2_merge_active : DI4Merge.Active cfgA.Q2 :=
  DI4Merge.active_of_W cfgA.Q2 (cfg_Q2_W cfgA cfgA_valid).1 (cfg_nodups cfgA cfgA_valid).2.2.2.1

theorem cfgA_Q5_merge_active : DI4Merge.Active cfgA.Q5 :=
  DI4Merge.active_of_W cfgA.Q5 (cfg_Q5_W cfgA cfgA_valid).1 (cfg_nodups cfgA cfgA_valid).2.2.2.2

theorem cfgA_R8_merge_active : DI4Merge.Active cfgA.R8 :=
  DI4Merge.active_of_W cfgA.R8 (cfg_R8_W cfgA cfgA_valid) (cfg_nodups cfgA cfgA_valid).2.1

theorem cfgA_Q1_diagonal_geometry_linear_core :
    DI5DiagonalGeometry.CoreGeometry cfgA.Q1.lo cfgA.Q1.dlo cfgA.Q1.carry cfgA.Q1.cin ∧
    DI5DiagonalGeometry.CoreGeometry cfgA.Q1.hi cfgA.Q1.dhi cfgA.Q1.carry cfgA.Q1.cin := by
  simp only [cfgA_fast,SplitCfg.Q1_fast]
  decide +kernel

theorem cfgA_Q1_diagonal_geometry :
    DI5DiagonalGeometry.Geometry cfgA.Q1.lo cfgA.Q1.dlo cfgA.Q1.carry cfgA.Q1.cin ∧
    DI5DiagonalGeometry.Geometry cfgA.Q1.hi cfgA.Q1.dhi cfgA.Q1.carry cfgA.Q1.cin :=
  ⟨DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgA_Q1_diagonal_geometry_linear_core.1,
   DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgA_Q1_diagonal_geometry_linear_core.2⟩

theorem cfgA_Q1_active : DI4Square.Active cfgA.Q1 :=
  DI5DiagonalGeometry.active_of_W_geometry cfgA.Q1 (cfg_Q1_W cfgA cfgA_valid).1
    (cfg_nodups cfgA cfgA_valid).2.2.1
    cfgA_Q1_diagonal_geometry.1 cfgA_Q1_diagonal_geometry.2

theorem cfgA_Q2_diagonal_geometry_linear_core :
    DI5DiagonalGeometry.CoreGeometry cfgA.Q2.lo cfgA.Q2.dlo cfgA.Q2.carry cfgA.Q2.cin ∧
    DI5DiagonalGeometry.CoreGeometry cfgA.Q2.hi cfgA.Q2.dhi cfgA.Q2.carry cfgA.Q2.cin := by
  simp only [cfgA_fast,SplitCfg.Q2_fast]
  decide +kernel

theorem cfgA_Q2_diagonal_geometry :
    DI5DiagonalGeometry.Geometry cfgA.Q2.lo cfgA.Q2.dlo cfgA.Q2.carry cfgA.Q2.cin ∧
    DI5DiagonalGeometry.Geometry cfgA.Q2.hi cfgA.Q2.dhi cfgA.Q2.carry cfgA.Q2.cin :=
  ⟨DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgA_Q2_diagonal_geometry_linear_core.1,
   DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgA_Q2_diagonal_geometry_linear_core.2⟩

theorem cfgA_Q2_active : DI4Square.Active cfgA.Q2 :=
  DI5DiagonalGeometry.active_of_W_geometry cfgA.Q2 (cfg_Q2_W cfgA cfgA_valid).1
    (cfg_nodups cfgA cfgA_valid).2.2.2.1
    cfgA_Q2_diagonal_geometry.1 cfgA_Q2_diagonal_geometry.2

theorem cfgA_Q5_diagonal_geometry_linear_core :
    DI5DiagonalGeometry.CoreGeometry cfgA.Q5.lo cfgA.Q5.dlo cfgA.Q5.carry cfgA.Q5.cin ∧
    DI5DiagonalGeometry.CoreGeometry cfgA.Q5.hi cfgA.Q5.dhi cfgA.Q5.carry cfgA.Q5.cin := by
  simp only [cfgA_fast,SplitCfg.Q5_fast]
  decide +kernel

theorem cfgA_Q5_diagonal_geometry :
    DI5DiagonalGeometry.Geometry cfgA.Q5.lo cfgA.Q5.dlo cfgA.Q5.carry cfgA.Q5.cin ∧
    DI5DiagonalGeometry.Geometry cfgA.Q5.hi cfgA.Q5.dhi cfgA.Q5.carry cfgA.Q5.cin :=
  ⟨DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgA_Q5_diagonal_geometry_linear_core.1,
   DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgA_Q5_diagonal_geometry_linear_core.2⟩

theorem cfgA_Q5_active : DI4Square.Active cfgA.Q5 :=
  DI5DiagonalGeometry.active_of_W_geometry cfgA.Q5 (cfg_Q5_W cfgA cfgA_valid).1
    (cfg_nodups cfgA cfgA_valid).2.2.2.2
    cfgA_Q5_diagonal_geometry.1 cfgA_Q5_diagonal_geometry.2

theorem cfgA_padded_merge_active : PaddedCombined.Active cfgA.Q5 :=
  PaddedCombined.active_of_merge cfgA.Q5 (cfg_Q5_W cfgA cfgA_valid).1 (cfg_Q5_W cfgA cfgA_valid).2.2 (by rw [(cfg_Q5_W cfgA cfgA_valid).2.1,(cfg_Q5_W cfgA cfgA_valid).2.2]) cfgA_Q5_merge_active

theorem cfgA_padded_make_active : DI4PadMake.Active cfgA.Q5 := by
  apply DI5PaddedGeometry.active_of_W_core cfgA.Q5 (cfg_Q5_W cfgA cfgA_valid).1 (cfg_Q5_W cfgA cfgA_valid).2.2 (by rw [(cfg_Q5_W cfgA cfgA_valid).2.1,(cfg_Q5_W cfgA cfgA_valid).2.2]) (cfg_nodups cfgA cfgA_valid).2.2.2.2
  simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, K0_eq, E0_eq, G0_eq, D0_eq]
  decide +kernel

theorem cfgA_make_delta : toffoliCount cfgA.make+4=toffoliCount cfgA.makeRef := by
  have qp := DI4PadMake.makeC_delta cfgA.Q5 (cfg_Q5_W cfgA cfgA_valid).1 (cfg_Q5_W cfgA cfgA_valid).2.2 (by rw [(cfg_Q5_W cfgA cfgA_valid).2.1,(cfg_Q5_W cfgA cfgA_valid).2.2]) cfgA_padded_make_active
  simp only [SplitCfg.make,SplitCfg.makeRef,DI4Leaves.make,
    show cfgA.n=128 from rfl,show (128:Nat)≠129 from by decide,show (129:Nat)≠128 from by decide,
    if_false,if_true,toffoliCount_append]
  omega

theorem cfgA_clear_delta : toffoliCount cfgA.clear+19=toffoliCount cfgA.clearRef := by
  have q1 := DI4Square.clearC_delta cfgA.Q1 cfgA_Q1_active cfgA_Q1_merge_active cfgA_Q1_c7_active
  have q2 := DI4Square.clearC_delta cfgA.Q2 cfgA_Q2_active cfgA_Q2_merge_active cfgA_Q2_c7_active
  have q5 := DI4PadClear.clearC_delta cfgA.Q5 cfgA_Q5_active cfgA_padded_merge_active cfgA_Q5_c7_active
  have cm := DI4Merge.safe_tc cfgA.R8 cfgA_R8_merge_active
  rw [DI4Merge.c8g_eq_c8z cfgA.R8 (cfg_R8_W cfgA cfgA_valid)] at cm
  simp only [SplitCfg.clear,SplitCfg.clearRef,DI4Leaves.clear,
    show cfgA.n=128 from rfl,show (128:Nat)≠129 from by decide,show (129:Nat)≠128 from by decide,
    if_false,if_true,toffoliCount_append]
  omega

theorem c7fast_cfgB_Q1_geometry : DI4C7Fast.Geometry cfgB.Q1 := by
  simp only [cfgB_fast,SplitCfg.Q1_fast]
  decide +kernel

theorem c7fast_cfgB_Q1_active : DI4LastCarry.Active cfgB.Q1 :=
  DI4C7Fast.active_of_geometry cfgB.Q1 (cfg_Q1_W cfgB cfgB_valid).1
    (cfg_nodups cfgB cfgB_valid).2.2.1 c7fast_cfgB_Q1_geometry

theorem cfgB_Q1_c7_active : DI4LastCarry.Active cfgB.Q1 := c7fast_cfgB_Q1_active

theorem c7fast_cfgB_Q2_geometry : DI4C7Fast.Geometry cfgB.Q2 := by
  simp only [cfgB_fast,SplitCfg.Q2_fast]
  decide +kernel

theorem c7fast_cfgB_Q2_active : DI4LastCarry.Active cfgB.Q2 :=
  DI4C7Fast.active_of_geometry cfgB.Q2 (cfg_Q2_W cfgB cfgB_valid).1
    (cfg_nodups cfgB cfgB_valid).2.2.2.1 c7fast_cfgB_Q2_geometry

theorem cfgB_Q2_c7_active : DI4LastCarry.Active cfgB.Q2 := c7fast_cfgB_Q2_active

theorem c7fast_cfgB_Q5_geometry : DI4C7Fast.Geometry cfgB.Q5 := by
  simp only [cfgB_fast,SplitCfg.Q5_fast]
  decide +kernel

theorem c7fast_cfgB_Q5_active : DI4LastCarry.Active cfgB.Q5 :=
  DI4C7Fast.active_of_geometry cfgB.Q5 (cfg_Q5_W cfgB cfgB_valid).1
    (cfg_nodups cfgB cfgB_valid).2.2.2.2 c7fast_cfgB_Q5_geometry

theorem cfgB_Q5_c7_active : DI4LastCarry.Active cfgB.Q5 := c7fast_cfgB_Q5_active

theorem cfgB_Q1_merge_active : DI4Merge.Active cfgB.Q1 :=
  DI4Merge.active_of_W cfgB.Q1 (cfg_Q1_W cfgB cfgB_valid).1 (cfg_nodups cfgB cfgB_valid).2.2.1

theorem cfgB_Q2_merge_active : DI4Merge.Active cfgB.Q2 :=
  DI4Merge.active_of_W cfgB.Q2 (cfg_Q2_W cfgB cfgB_valid).1 (cfg_nodups cfgB cfgB_valid).2.2.2.1

theorem cfgB_Q5_merge_active : DI4Merge.Active cfgB.Q5 :=
  DI4Merge.active_of_W cfgB.Q5 (cfg_Q5_W cfgB cfgB_valid).1 (cfg_nodups cfgB cfgB_valid).2.2.2.2

theorem cfgB_R8_merge_active : DI4Merge.Active cfgB.R8 :=
  DI4Merge.active_of_W cfgB.R8 (cfg_R8_W cfgB cfgB_valid) (cfg_nodups cfgB cfgB_valid).2.1

theorem cfgB_Q1_diagonal_geometry_linear_core :
    DI5DiagonalGeometry.CoreGeometry cfgB.Q1.lo cfgB.Q1.dlo cfgB.Q1.carry cfgB.Q1.cin ∧
    DI5DiagonalGeometry.CoreGeometry cfgB.Q1.hi cfgB.Q1.dhi cfgB.Q1.carry cfgB.Q1.cin := by
  simp only [cfgB_fast,SplitCfg.Q1_fast]
  decide +kernel

theorem cfgB_Q1_diagonal_geometry :
    DI5DiagonalGeometry.Geometry cfgB.Q1.lo cfgB.Q1.dlo cfgB.Q1.carry cfgB.Q1.cin ∧
    DI5DiagonalGeometry.Geometry cfgB.Q1.hi cfgB.Q1.dhi cfgB.Q1.carry cfgB.Q1.cin :=
  ⟨DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgB_Q1_diagonal_geometry_linear_core.1,
   DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgB_Q1_diagonal_geometry_linear_core.2⟩

theorem cfgB_Q1_active : DI4Square.Active cfgB.Q1 :=
  DI5DiagonalGeometry.active_of_W_geometry cfgB.Q1 (cfg_Q1_W cfgB cfgB_valid).1
    (cfg_nodups cfgB cfgB_valid).2.2.1
    cfgB_Q1_diagonal_geometry.1 cfgB_Q1_diagonal_geometry.2

theorem cfgB_Q2_diagonal_geometry_linear_core :
    DI5DiagonalGeometry.CoreGeometry cfgB.Q2.lo cfgB.Q2.dlo cfgB.Q2.carry cfgB.Q2.cin ∧
    DI5DiagonalGeometry.CoreGeometry cfgB.Q2.hi cfgB.Q2.dhi cfgB.Q2.carry cfgB.Q2.cin := by
  simp only [cfgB_fast,SplitCfg.Q2_fast]
  decide +kernel

theorem cfgB_Q2_diagonal_geometry :
    DI5DiagonalGeometry.Geometry cfgB.Q2.lo cfgB.Q2.dlo cfgB.Q2.carry cfgB.Q2.cin ∧
    DI5DiagonalGeometry.Geometry cfgB.Q2.hi cfgB.Q2.dhi cfgB.Q2.carry cfgB.Q2.cin :=
  ⟨DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgB_Q2_diagonal_geometry_linear_core.1,
   DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgB_Q2_diagonal_geometry_linear_core.2⟩

theorem cfgB_Q2_active : DI4Square.Active cfgB.Q2 :=
  DI5DiagonalGeometry.active_of_W_geometry cfgB.Q2 (cfg_Q2_W cfgB cfgB_valid).1
    (cfg_nodups cfgB cfgB_valid).2.2.2.1
    cfgB_Q2_diagonal_geometry.1 cfgB_Q2_diagonal_geometry.2

theorem cfgB_Q5_diagonal_geometry_linear_core :
    DI5DiagonalGeometry.CoreGeometry cfgB.Q5.lo cfgB.Q5.dlo cfgB.Q5.carry cfgB.Q5.cin ∧
    DI5DiagonalGeometry.CoreGeometry cfgB.Q5.hi cfgB.Q5.dhi cfgB.Q5.carry cfgB.Q5.cin := by
  simp only [cfgB_fast,SplitCfg.Q5_fast]
  decide +kernel

theorem cfgB_Q5_diagonal_geometry :
    DI5DiagonalGeometry.Geometry cfgB.Q5.lo cfgB.Q5.dlo cfgB.Q5.carry cfgB.Q5.cin ∧
    DI5DiagonalGeometry.Geometry cfgB.Q5.hi cfgB.Q5.dhi cfgB.Q5.carry cfgB.Q5.cin :=
  ⟨DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgB_Q5_diagonal_geometry_linear_core.1,
   DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgB_Q5_diagonal_geometry_linear_core.2⟩

theorem cfgB_Q5_active : DI4Square.Active cfgB.Q5 :=
  DI5DiagonalGeometry.active_of_W_geometry cfgB.Q5 (cfg_Q5_W cfgB cfgB_valid).1
    (cfg_nodups cfgB cfgB_valid).2.2.2.2
    cfgB_Q5_diagonal_geometry.1 cfgB_Q5_diagonal_geometry.2

theorem cfgB_padded_merge_active : PaddedCombined.Active cfgB.Q5 :=
  PaddedCombined.active_of_merge cfgB.Q5 (cfg_Q5_W cfgB cfgB_valid).1 (cfg_Q5_W cfgB cfgB_valid).2.2 (by rw [(cfg_Q5_W cfgB cfgB_valid).2.1,(cfg_Q5_W cfgB cfgB_valid).2.2]) cfgB_Q5_merge_active

theorem cfgB_padded_make_active : DI4PadMake.Active cfgB.Q5 := by
  apply DI5PaddedGeometry.active_of_W_core cfgB.Q5 (cfg_Q5_W cfgB cfgB_valid).1 (cfg_Q5_W cfgB cfgB_valid).2.2 (by rw [(cfg_Q5_W cfgB cfgB_valid).2.1,(cfg_Q5_W cfgB cfgB_valid).2.2]) (cfg_nodups cfgB cfgB_valid).2.2.2.2
  simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, K0_eq, E0_eq, G0_eq, D0_eq]
  decide +kernel

theorem cfgB_make_delta : toffoliCount cfgB.make+4=toffoliCount cfgB.makeRef := by
  have qp := DI4PadMake.makeC_delta cfgB.Q5 (cfg_Q5_W cfgB cfgB_valid).1 (cfg_Q5_W cfgB cfgB_valid).2.2 (by rw [(cfg_Q5_W cfgB cfgB_valid).2.1,(cfg_Q5_W cfgB cfgB_valid).2.2]) cfgB_padded_make_active
  simp only [SplitCfg.make,SplitCfg.makeRef,DI4Leaves.make,
    show cfgB.n=128 from rfl,show (128:Nat)≠129 from by decide,show (129:Nat)≠128 from by decide,
    if_false,if_true,toffoliCount_append]
  omega

theorem cfgB_clear_delta : toffoliCount cfgB.clear+19=toffoliCount cfgB.clearRef := by
  have q1 := DI4Square.clearC_delta cfgB.Q1 cfgB_Q1_active cfgB_Q1_merge_active cfgB_Q1_c7_active
  have q2 := DI4Square.clearC_delta cfgB.Q2 cfgB_Q2_active cfgB_Q2_merge_active cfgB_Q2_c7_active
  have q5 := DI4PadClear.clearC_delta cfgB.Q5 cfgB_Q5_active cfgB_padded_merge_active cfgB_Q5_c7_active
  have cm := DI4Merge.safe_tc cfgB.R8 cfgB_R8_merge_active
  rw [DI4Merge.c8g_eq_c8z cfgB.R8 (cfg_R8_W cfgB cfgB_valid)] at cm
  simp only [SplitCfg.clear,SplitCfg.clearRef,DI4Leaves.clear,
    show cfgB.n=128 from rfl,show (128:Nat)≠129 from by decide,show (129:Nat)≠128 from by decide,
    if_false,if_true,toffoliCount_append]
  omega

theorem c7fast_cfgC_Q1_geometry : DI4C7Fast.Geometry cfgC.Q1 := by
  simp only [cfgC_fast,SplitCfg.Q1_fast]
  decide +kernel

theorem c7fast_cfgC_Q1_active : DI4LastCarry.Active cfgC.Q1 :=
  DI4C7Fast.active_of_geometry cfgC.Q1 (cfg_Q1_W cfgC cfgC_valid).1
    (cfg_nodups cfgC cfgC_valid).2.2.1 c7fast_cfgC_Q1_geometry

theorem cfgC_Q1_c7_active : DI4LastCarry.Active cfgC.Q1 := c7fast_cfgC_Q1_active

theorem c7fast_cfgC_Q2_geometry : DI4C7Fast.Geometry cfgC.Q2 := by
  simp only [cfgC_fast,SplitCfg.Q2_fast]
  decide +kernel

theorem c7fast_cfgC_Q2_active : DI4LastCarry.Active cfgC.Q2 :=
  DI4C7Fast.active_of_geometry cfgC.Q2 (cfg_Q2_W cfgC cfgC_valid).1
    (cfg_nodups cfgC cfgC_valid).2.2.2.1 c7fast_cfgC_Q2_geometry

theorem cfgC_Q2_c7_active : DI4LastCarry.Active cfgC.Q2 := c7fast_cfgC_Q2_active

theorem c7fast_cfgC_Q5_geometry : DI4C7Fast.Geometry cfgC.Q5 := by
  simp only [cfgC_fast,SplitCfg.Q5_fast]
  decide +kernel

theorem c7fast_cfgC_Q5_active : DI4LastCarry.Active cfgC.Q5 :=
  DI4C7Fast.active_of_geometry cfgC.Q5 (cfg_Q5_W cfgC cfgC_valid).1
    (cfg_nodups cfgC cfgC_valid).2.2.2.2 c7fast_cfgC_Q5_geometry


theorem cfgC_Q5_c7_active : DI4LastCarry.Active cfgC.Q5 := c7fast_cfgC_Q5_active

theorem cfgC_Q1_merge_active : DI4Merge.Active cfgC.Q1 :=
  DI4Merge.active_of_W cfgC.Q1 (cfg_Q1_W cfgC cfgC_valid).1 (cfg_nodups cfgC cfgC_valid).2.2.1

theorem cfgC_Q2_merge_active : DI4Merge.Active cfgC.Q2 :=
  DI4Merge.active_of_W cfgC.Q2 (cfg_Q2_W cfgC cfgC_valid).1 (cfg_nodups cfgC cfgC_valid).2.2.2.1

theorem cfgC_Q5_merge_active : DI4Merge.Active cfgC.Q5 :=
  DI4Merge.active_of_W cfgC.Q5 (cfg_Q5_W cfgC cfgC_valid).1 (cfg_nodups cfgC cfgC_valid).2.2.2.2

theorem cfgC_R8_merge_active : DI4Merge.Active cfgC.R8 :=
  DI4Merge.active_of_W cfgC.R8 (cfg_R8_W cfgC cfgC_valid) (cfg_nodups cfgC cfgC_valid).2.1

theorem cfgC_Q1_diagonal_geometry_linear_core :
    DI5DiagonalGeometry.CoreGeometry cfgC.Q1.lo cfgC.Q1.dlo cfgC.Q1.carry cfgC.Q1.cin ∧
    DI5DiagonalGeometry.CoreGeometry cfgC.Q1.hi cfgC.Q1.dhi cfgC.Q1.carry cfgC.Q1.cin := by
  simp only [cfgC_fast,SplitCfg.Q1_fast]
  decide +kernel

theorem cfgC_Q1_diagonal_geometry :
    DI5DiagonalGeometry.Geometry cfgC.Q1.lo cfgC.Q1.dlo cfgC.Q1.carry cfgC.Q1.cin ∧
    DI5DiagonalGeometry.Geometry cfgC.Q1.hi cfgC.Q1.dhi cfgC.Q1.carry cfgC.Q1.cin :=
  ⟨DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgC_Q1_diagonal_geometry_linear_core.1,
   DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgC_Q1_diagonal_geometry_linear_core.2⟩

theorem cfgC_Q1_active : DI4Square.Active cfgC.Q1 :=
  DI5DiagonalGeometry.active_of_W_geometry cfgC.Q1 (cfg_Q1_W cfgC cfgC_valid).1
    (cfg_nodups cfgC cfgC_valid).2.2.1
    cfgC_Q1_diagonal_geometry.1 cfgC_Q1_diagonal_geometry.2

theorem cfgC_Q2_diagonal_geometry_linear_core :
    DI5DiagonalGeometry.CoreGeometry cfgC.Q2.lo cfgC.Q2.dlo cfgC.Q2.carry cfgC.Q2.cin ∧
    DI5DiagonalGeometry.CoreGeometry cfgC.Q2.hi cfgC.Q2.dhi cfgC.Q2.carry cfgC.Q2.cin := by
  simp only [cfgC_fast,SplitCfg.Q2_fast]
  decide +kernel

theorem cfgC_Q2_diagonal_geometry :
    DI5DiagonalGeometry.Geometry cfgC.Q2.lo cfgC.Q2.dlo cfgC.Q2.carry cfgC.Q2.cin ∧
    DI5DiagonalGeometry.Geometry cfgC.Q2.hi cfgC.Q2.dhi cfgC.Q2.carry cfgC.Q2.cin :=
  ⟨DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgC_Q2_diagonal_geometry_linear_core.1,
   DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgC_Q2_diagonal_geometry_linear_core.2⟩

theorem cfgC_Q2_active : DI4Square.Active cfgC.Q2 :=
  DI5DiagonalGeometry.active_of_W_geometry cfgC.Q2 (cfg_Q2_W cfgC cfgC_valid).1
    (cfg_nodups cfgC cfgC_valid).2.2.2.1
    cfgC_Q2_diagonal_geometry.1 cfgC_Q2_diagonal_geometry.2

theorem cfgC_Q5_diagonal_geometry_linear_core :
    DI5DiagonalGeometry.CoreGeometry cfgC.Q5.lo cfgC.Q5.dlo cfgC.Q5.carry cfgC.Q5.cin ∧
    DI5DiagonalGeometry.CoreGeometry cfgC.Q5.hi cfgC.Q5.dhi cfgC.Q5.carry cfgC.Q5.cin := by
  simp only [cfgC_fast,SplitCfg.Q5_fast]
  decide +kernel

theorem cfgC_Q5_diagonal_geometry :
    DI5DiagonalGeometry.Geometry cfgC.Q5.lo cfgC.Q5.dlo cfgC.Q5.carry cfgC.Q5.cin ∧
    DI5DiagonalGeometry.Geometry cfgC.Q5.hi cfgC.Q5.dhi cfgC.Q5.carry cfgC.Q5.cin :=
  ⟨DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgC_Q5_diagonal_geometry_linear_core.1,
   DI5DiagonalGeometry.geometry_of_core _ _ _ _ cfgC_Q5_diagonal_geometry_linear_core.2⟩

theorem cfgC_Q5_active : DI4Square.Active cfgC.Q5 :=
  DI5DiagonalGeometry.active_of_W_geometry cfgC.Q5 (cfg_Q5_W cfgC cfgC_valid).1
    (cfg_nodups cfgC cfgC_valid).2.2.2.2
    cfgC_Q5_diagonal_geometry.1 cfgC_Q5_diagonal_geometry.2

theorem cfgC_padded_merge_active : PaddedCombined.Active cfgC.Q2 :=
  PaddedCombined.active_of_merge cfgC.Q2 (cfg_Q2_W cfgC cfgC_valid).1 (q2_pad_dims cfgC cfgC_valid rfl).1 (by rw [(cfg_Q2_W cfgC cfgC_valid).2.1,(q2_pad_dims cfgC cfgC_valid rfl).1]) cfgC_Q2_merge_active

theorem cfgC_padded_make_active : DI4PadMake.Active cfgC.Q2 := by
  apply DI5PaddedGeometry.active_of_W_core cfgC.Q2 (cfg_Q2_W cfgC cfgC_valid).1 (q2_pad_dims cfgC cfgC_valid rfl).1 (q2_pad_dims cfgC cfgC_valid rfl).2 (cfg_nodups cfgC cfgC_valid).2.2.2.1
  simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, K0_eq, E0_eq, G0_eq, D0_eq]
  decide +kernel

theorem cfgC_make_delta : toffoliCount cfgC.make+4=toffoliCount cfgC.makeRef := by
  have qp := DI4PadMake.makeC_delta cfgC.Q2 (cfg_Q2_W cfgC cfgC_valid).1 (q2_pad_dims cfgC cfgC_valid rfl).1 (by rw [(cfg_Q2_W cfgC cfgC_valid).2.1,(q2_pad_dims cfgC cfgC_valid rfl).1]) cfgC_padded_make_active
  simp only [SplitCfg.make,SplitCfg.makeRef,DI4Leaves.make,
    show cfgC.n=129 from rfl,show (128:Nat)≠129 from by decide,show (129:Nat)≠128 from by decide,
    if_false,if_true,toffoliCount_append]
  omega

theorem cfgC_clear_delta : toffoliCount cfgC.clear+19=toffoliCount cfgC.clearRef := by
  have q1 := DI4Square.clearC_delta cfgC.Q1 cfgC_Q1_active cfgC_Q1_merge_active cfgC_Q1_c7_active
  have q2 := DI4PadClear.clearC_delta cfgC.Q2 cfgC_Q2_active cfgC_padded_merge_active cfgC_Q2_c7_active
  have q5 := DI4Square.clearC_delta cfgC.Q5 cfgC_Q5_active cfgC_Q5_merge_active cfgC_Q5_c7_active
  have cm := DI4Merge.safe_tc cfgC.R8 cfgC_R8_merge_active
  rw [DI4Merge.c8g_eq_c8z cfgC.R8 (cfg_R8_W cfgC cfgC_valid)] at cm
  simp only [SplitCfg.clear,SplitCfg.clearRef,DI4Leaves.clear,
    show cfgC.n=129 from rfl,show (128:Nat)≠129 from by decide,show (129:Nat)≠128 from by decide,
    if_false,if_true,toffoliCount_append]
  omega

end SplitSlots

/-! ## Direct-fold renaming helper (moves `workT` onto `K0.core.pad.take workT.length`) -/

section FoldMove
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq

private theorem directFold_rename_run (pairs : List (Wire × Wire)) (f : MeasuredSquareFold)
    (hcnt : ∀ q, f.src.count q ≤ K0.core.product.count q)
    (hlen : f.src.length = 256) (hcan : f.canonical = true) (hsh : f.shift = 0)
    (hholes : ∀ ab ∈ pairs, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out)
    (hhosts : ∀ ab ∈ pairs, ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out)
    (base : BasisState) (hv : K0.MeasuredFoldView base f) (hc : K0.PairClean base)
    (O : Nat) (hO : O < SquareReduction.p) (s : State) (m : List Bool)
    (hf : SquareFrame K0.core.out base O s.basis) :
    run (hostRename pairs (directFoldQTq K0 f)) m s = run (directFoldQTq K0 f) m s := by
  have hn := (List.nodup_cons.mp controlND).2
  have cleanIn := K0.squareFrame_clean hn base s.basis O hf hc
  have frame := directFoldQ_frameTq K0 hwK hn base f hv hcan hc hlen hsh O hO s m hf
  have cleanOut := K0.squareFrame_clean hn base (run (directFoldQTq K0 f) m s).basis
    ((measuredFoldPayload base f + (SquareReduction.p - 1 - O)) % SquareReduction.p) frame.2 hc
  apply hostRename_run_eq pairs (directFoldQTq K0 f) s m
  · intro ab hab; exact (regValue_zero _ _).mp cleanIn.work ab.1 (hholes ab hab).1
  · intro ab hab; exact (regValue_zero _ _).mp cleanIn.pad ab.2 (List.mem_append_left _ (hhosts ab hab).1)
  · intro ab hab; exact (regValue_zero _ _).mp cleanOut.work ab.1 (hholes ab hab).1
  · intro ab hab
    exact directFoldQ_free K0 hn f hcnt ab.2 (by simp [directFree, (hhosts ab hab).1])

private theorem directFold_rename_support (pairs : List (Wire × Wire)) (f : MeasuredSquareFold)
    (hcnt : ∀ q, f.src.count q ≤ K0.core.product.count q)
    (hnd : (holesOf pairs ++ hostsOf pairs).Nodup)
    (hhosts : ∀ ab ∈ pairs, ab.2 ∈ K0.core.pad) :
    wires (hostRename pairs (directFoldQTq K0 f)) ⊆
      (wires (directFoldQTq K0 f) \ (holesOf pairs).toFinset) ∪ (hostsOf pairs).toFinset := by
  have hn := (List.nodup_cons.mp controlND).2
  exact hostRename_support pairs (directFoldQTq K0 f) hnd (fun ab hab =>
    directFoldQ_free K0 hn f hcnt ab.2 (by simp [directFree, hhosts ab hab]))

end FoldMove

/-! ## Branch A body (`keepA` = 33 carries, avoids `workTA` and `hs`) -/

section BodyA
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq

private theorem la_eq_K0 : ReorderedAFixed.L = K0 := rfl

def keepA : List Wire := A109Research.keepK.filter (fun q => !workTA.contains q)

theorem keepA_geometry : keepA.Nodup ∧ keepA.length = 33 ∧
    (∀ q ∈ keepA, q ∈ A109Research.hosts) ∧
    (∀ q ∈ workTA, q ∉ keepA) ∧
    (∀ i, i < 44 → ReorderedAFixed.hs.getD i 0 ∉ keepA) ∧
    (∀ q ∈ keepA, q ∈ allowedWires) := by
  have hall : ∀ q ∈ keepA, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [keepA, keepKA_fast, workTA_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [keepA, keepKA_fast, workTA_lit, hs_lit]; decide +kernel))
  have hr : keepA.Nodup ∧ keepA.length = 33 ∧
      (∀ q ∈ keepA, q ∈ A109Research.hosts) ∧
      (∀ q ∈ workTA, q ∉ keepA) ∧
      (∀ i, i < 44 → ReorderedAFixed.hs.getD i 0 ∉ keepA) := by
    rw [keepA, keepKA_fast, hostsA109_fast, hsA_fast, workTA_lit]; decide +kernel
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, hall⟩

def rawFA : Program := ReorderedGenericCache.cachedAdd 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
def newFA : Program := A109Research.head ++ A109LowEraseResearch.clear ++ rawFA ++ A109Research.top
def newIA : Program := A109Research.preInv ++ ReorderedConsumedSub.consumed 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
def coreA : Program := (newFA ++ A109Research.M ++ newIA) ++ (A109LowEraseResearch.clear ++ A109Research.tail)
def restA : Program := A109LowEraseResearch.clear ++ rawFA ++ A109Research.top ++ A109Research.M ++ newIA ++ A109LowEraseResearch.clear ++ A109Research.tail
def loopPCA : Program := SignAHead.head ++ restA
def loopA : Program := hostRename (StairSqLoopA.pairs hs) loopPCA
def foldPairsA : List (Wire × Wire) := workTA.zip (K0.core.pad.take 32)
def dF1A : Program := hostRename foldPairsA (directFoldQTq K0 (negP K0))
def dF2A : Program := hostRename foldPairsA (directFoldQTq K0 (rot128F K0))
def bodyA : Program := (dF1A ++ (dF2A ++ loopA)) ++ ReorderedRecordPadding.program 7 K0.core.cin
def bodyAPlain : Program := A109SignResearch.directBody loopA

theorem foldPairsA_geom :
    (holesOf foldPairsA ++ hostsOf foldPairsA).Nodup ∧
    holesOf foldPairsA = workTA ∧
    hostsOf foldPairsA = K0.core.pad.take 32 ∧
    (∀ ab ∈ foldPairsA, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out ∧ ab.2 ∈ allowedWires) ∧
    (∀ q ∈ hostsOf foldPairsA, q ∉ hs ∧ q ≠ ControlLoan1589BFFold.eU K0 ∧ q ∈ K0.wires ∧ q ∈ allowedWires) := by
  have hall : ∀ q ∈ hostsOf foldPairsA, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsA, workTA_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [foldPairsA, workTA_lit, K0_eq, hs_lit]; decide +kernel))
  have hK : ∀ q ∈ hostsOf foldPairsA, q ∈ K0.wires :=
    StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsA, workTA_lit, K0_eq]; decide +kernel)
  have hr : (holesOf foldPairsA ++ hostsOf foldPairsA).Nodup ∧
      holesOf foldPairsA = workTA ∧
      hostsOf foldPairsA = K0.core.pad.take 32 ∧
      (∀ ab ∈ foldPairsA, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out) ∧
      (∀ q ∈ hostsOf foldPairsA, q ∉ hs ∧ q ≠ ControlLoan1589BFFold.eU K0) := by
    rw [foldPairsA, workTA_lit, K0_eq, hs_lit]; decide +kernel
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_, ?_⟩
  · intro ab hab; have h := hr.2.2.2.1 ab hab
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hall ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩)⟩
  · intro q hq; have h := hr.2.2.2.2 q hq
    exact ⟨h.1, h.2, hK q hq, hall q hq⟩

private theorem keepA_sub (q : Wire) (hq : q ∈ keepA) : q ∈ A109Research.hosts := keepA_geometry.2.2.1 q hq

private theorem core_plainA (s : State) (m : List Bool)
    (hz : ∀ q ∈ ReorderedBPrefixResearch.pad, s.basis q = false) (hb : ∀ q ∈ ReorderedBPrefixResearch.bank, s.basis q = false)
    (hi : s.basis ReorderedBPrefixResearch.cin = false) (ha : regValue ReorderedBPrefixResearch.acc s.basis = 0)
    (zero : ∀ q ∈ ReorderedAFixed.hosts, s.basis q = false)
    (after : WReady ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src
      (regValue ReorderedBPrefixResearch.src s.basis) (middleState A109Research.oldF A109Research.oldM s m))
    (flag : (run A109Research.oldF (m.take (measurementCount A109Research.oldF)) s).basis 4762 = false) :
    run coreA m s = run (A109Research.oldF ++ A109Research.oldM ++
      ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) m s := by
  let H := regValue ReorderedBPrefixResearch.src s.basis
  let vs := ReorderedCacheBits.values 4 33 H (976 * H / 1024)
  have keepSubK (q : Wire) (hq : q ∈ keepA) : q ∈ A109Research.keepK := (List.mem_filter.mp hq).1
  have fwdM : measurementCount newFA = measurementCount A109Research.F := by
    have h := (ReorderedGenericCache.count_balance 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide)).2.1
    simp only [newFA, rawFA, A109Research.F, A109Research.rawF, measurementCount_append]; rw [h]
  have invM : measurementCount newIA = measurementCount A109Research.I := by
    have h := ReorderedConsumedSub.measurement_eq 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide)
    simp only [newIA, A109Research.I, A109Research.rawI, measurementCount_append]; rw [h]
  have fwdVal : (((A109Research.cs.drop 4).take 33).map (run (carryPrefix (4 + 33) A109Research.xs A109Research.ys A109Research.cs ReorderedBPrefixResearch.cin) []
      (run (A109Research.head ++ A109LowEraseResearch.clear)
        ((m.take (measurementCount A109Research.F)).take (measurementCount (A109Research.head ++ A109LowEraseResearch.clear))) s)).basis) = vs := by
    let m0 := (m.take (measurementCount A109Research.F)).take (measurementCount (A109Research.head ++ A109LowEraseResearch.clear))
    let u := run A109Research.head m0 s
    let t := run (A109Research.head ++ A109LowEraseResearch.clear) m0 s
    have te : t = A109LowEraseResearch.erase u := A109Research.prefix_erased s m0 hz hb hi ha
    have hH : H < 2 ^ 128 := by simpa only [H, ReorderedBPrefixResearch.source_length] using regValue_lt ReorderedBPrefixResearch.src s.basis
    have ready := ReorderedHeadArithmeticResearch.ready ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank
      ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits s m0 hz hb hi ha
    have eb (q : Wire) (hq : q ∈ A109Research.domain) : t.basis q = u.basis q := by
      rw [te]; exact A109LowEraseResearch.bit_same _ q (A109Research.domain_away_low q hq)
    have er (r : List Wire) (sub : ∀ q ∈ r, q ∈ A109Research.domain) : regValue r t.basis = regValue r u.basis :=
      regValue_congr _ _ _ (fun q hq => eb q (sub q hq))
    exact ReorderedCacheBits.forward_values 4 33 H (((2 ^ 138 - 48 * H) % 2 ^ 138) / 1024) (976 * H / 1024)
      A109Research.xs A109Research.ys A109Research.cs ReorderedBPrefixResearch.cin t
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide) A109Research.raw_nd
      (fun q hq => (eb q (A109Research.c_in q hq)).trans (ready.1 q hq))
      ((eb _ A109Research.cin_in).trans ready.2.1)
      ((er _ A109Research.x_in).trans ready.2.2.1)
      ((er _ A109Research.y_in).trans ready.2.2.2)
      (fun j hj => by simpa only [show 128 + 10 = 138 by decide] using ReorderedCacheArithmetic.high_add_low 128 (4 + j + 1) H (by omega) hH)
  have forward : run newFA (m.take (measurementCount A109Research.F)) s =
      scatterState keepA vs (run A109Research.F (m.take (measurementCount A109Research.F)) s) := by
    have h := CacheBetweenFrameResearch.forward (A109Research.head ++ A109LowEraseResearch.clear) A109Research.top
      33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide) keepA_geometry.1
      (fun q hq bad => A109Research.geometry.2.2 q (keepA_sub q hq) (by clear * - bad; simp only [A109Research.domain, List.mem_cons, List.mem_append] at bad ⊢; tauto))
      (fun q hq => A109Research.rawF_off q (keepA_sub q hq)) (fun q hq => A109Research.top_off q (keepA_sub q hq))
      s (m.take (measurementCount A109Research.F))
      (fun q hq => A109Research.prefix_zeroK s _ hz hb hi ha zero q (keepSubK q hq))
    rw [fwdVal] at h; exact h
  have mid := A109Research.middle_erased s m hz hb hi ha after flag
  have cacheEq : run (newFA ++ A109Research.M ++ newIA) m s = run (A109Research.F ++ A109Research.M ++ A109Research.I) m s := by
    apply CacheFromCleanForwardResearch.equivalent A109Research.F newFA A109Research.M A109Research.I newIA keepA vs
      fwdM (fun q hq => A109Research.middle_fresh q (keepA_sub q hq))
      (fun q hq => A109Research.I_off q (keepA_sub q hq)) keepA_geometry.1 s m
      (fun q hq => A109Research.forward_zeroK s _ hz hb hi ha zero q (keepSubK q hq)) forward
    rw [mid]
    let ms := middleState A109Research.oldF A109Research.oldM s m
    let mr := m.drop (measurementCount A109Research.F + measurementCount A109Research.M)
    let t := scatterState keepA vs (A109LowEraseResearch.erase ms)
    have comm : run A109Research.preInv mr t = scatterState keepA vs (A109LowEraseResearch.erase (run A109Research.preInv mr ms)) := by
      rw [show t = scatterState keepA vs (A109LowEraseResearch.erase ms) from rfl,
        run_scatter A109Research.preInv keepA vs _ _ (fun q hq => A109Research.preInv_off q (keepA_sub q hq)),
        A109LowEraseResearch.commute A109Research.preInv mr ms (fun q hq => A109Research.preInv_off q (A109Research.low_hosts q hq))]
    have bits (q : Wire) (hq : q ∈ A109Research.domain) : (run A109Research.preInv mr t).basis q = (run A109Research.preInv mr ms).basis q := by
      rw [comm, scatter_outside keepA vs _ q (fun bad => A109Research.geometry.2.2 q (keepA_sub q bad) hq)]
      exact A109LowEraseResearch.bit_same _ q (A109Research.domain_away_low q hq)
    have regs (r : List Wire) (sub : ∀ q ∈ r, q ∈ A109Research.domain) :
        regValue r (run A109Research.preInv mr t).basis = regValue r (run A109Research.preInv mr ms).basis :=
      regValue_congr _ _ _ (fun q hq => bits q (sub q hq))
    have rr := A109Research.pre_raw_ready H ms mr after
    have saved : keepA.map t.basis = vs := scatter_saved_map keepA vs _ keepA_geometry.1
      (by simp only [vs, ReorderedCacheBits.values, List.length_map, keepA_geometry.2.1, List.length_range])
    have same : keepA.map (run A109Research.preInv mr t).basis = keepA.map t.basis :=
      List.map_congr_left (fun q hq => run_preserves_outside A109Research.preInv mr t q (A109Research.preInv_off q (keepA_sub q hq)))
    simp only [newIA, A109Research.I, A109Research.rawI, ControlledBorrowResearch.run_cat]
    exact ReorderedConsumedSub.frame 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide)
      (by rw [A109Research.raw_lengths.1, A109Research.raw_lengths.2.1])
      (by rw [A109Research.raw_lengths.2.1, A109Research.raw_lengths.2.2])
      A109Research.raw_nd keepA_geometry.1 keepA_geometry.2.1 (fun q hq => A109Research.geometry.2.2 q (keepA_sub q hq))
      (run A109Research.preInv mr t) _ (fun q hq => (bits q (A109Research.c_in q hq)).trans (rr.1 q hq))
      ((bits _ A109Research.cin_in).trans rr.2.1) H (976 * H / 1024)
      ((regs _ A109Research.x_in).trans rr.2.2.1) ((regs _ A109Research.y_in).trans rr.2.2.2) (same.trans saved)
  have eq := ClearContextResearch.append_at (newFA ++ A109Research.M ++ newIA)
    (A109Research.F ++ A109Research.M ++ A109Research.I) (A109LowEraseResearch.clear ++ A109Research.tail) s m
    (by simp only [measurementCount_append, fwdM, invM]) cacheEq
  have shape : (A109Research.F ++ A109Research.M ++ A109Research.I) ++ (A109LowEraseResearch.clear ++ A109Research.tail) =
      A109Research.F ++ A109Research.M ++ (A109Research.I ++ A109LowEraseResearch.clear ++ A109Research.tail) := by
    have g (A B C D E : Program) : (A ++ B ++ C) ++ (D ++ E) = A ++ B ++ (C ++ D ++ E) := by simp only [List.append_assoc]
    exact g _ _ _ _ _
  exact eq.trans ((congrArg (fun P => run P m s) shape).trans (A109Research.plain_loop s m hz hb hi ha after flag))

private theorem coreA_frame (base : BasisState) (hc : ReorderedAFixed.L.PairClean base)
    (hsum : base A161Low4FixedFold.q = false) (hV : base A161Low4FixedFold.r = false)
    (hP : base A161Low4FixedFold.p = false) (hd : base ReorderedAFixed.d = false)
    (O : Nat) (hO : O < SquareReduction.p) :
    Triple (SquareFrame ReorderedAFixed.L.core.out base O) coreA
      (SquareFrame ReorderedAFixed.L.core.out base
        (((if base ReorderedAFixed.g then A161Low4Facts.Klow - 4294968272 * regValue ReorderedAFixed.src base
           else 4294968272 * regValue ReorderedAFixed.src base) + (SquareReduction.p - 1 - O)) % SquareReduction.p)) := by
  intro s m hf
  have clean := ReorderedAFixed.L.squareFrame_clean ReorderedAFixed.hn base s.basis O hf hc
  have hzFull : ∀ u ∈ accZ ReorderedAFixed.L, s.basis u = false := by
    intro u hu; rcases accZ_mem ReorderedAFixed.L u hu with hu | hu
    · exact (regValue_zero _ _).mp clean.pad u hu
    · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
  have hz : ∀ u ∈ ReorderedAFixed.pad, s.basis u = false := fun u hu => hzFull u ((FullPadDevelop.pad_sublist ReorderedAFixed.L).subset hu)
  have hb : ∀ u ∈ ReorderedAFixed.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
  have ha : regValue ReorderedAFixed.acc s.basis = 0 := A161Low4Ghost.ghostAcc_zero ReorderedAFixed.L s.basis clean
  have zeroU : ∀ u ∈ ReorderedAFixed.hs, s.basis u = false := fun u hu =>
    (hf.2 u (A161Low4FixedFold.hostClean base hc hd u hu).1).trans (A161Low4FixedFold.hostClean base hc hd u hu).2
  have zeroOld : ∀ u ∈ ReorderedAFixed.hosts, s.basis u = false := by
    have qz : s.basis ReorderedAFixed.q = false := (hf.2 ReorderedAFixed.q (by decide)).trans hsum
    have rz : s.basis ReorderedAFixed.r = false := (hf.2 ReorderedAFixed.r (by decide)).trans hV
    have pz : s.basis ReorderedAFixed.p = false := (hf.2 ReorderedAFixed.p (by decide)).trans hP
    change ∀ u ∈ ReorderedAFixed.q :: ReorderedAFixed.r :: ReorderedAFixed.p :: ReorderedAFixed.hs, s.basis u = false
    rw [List.forall_mem_cons, List.forall_mem_cons, List.forall_mem_cons]
    exact ⟨qz, rz, pz, zeroU⟩
  have offHs : ∀ u ∈ ReorderedAFixed.hs, u ∉ wires (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) :=
    fun u hu => (ReorderedAFixed.off_plain u (StairSqLoopA.hosts_of_hs u hu)).1
  have goodOriginal : WReady ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
      (regValue ReorderedAFixed.src s.basis)
      (middleState (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
        (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g) s m) := by
    rw [ReorderedARetape.a_middle_eq ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
      (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g) ReorderedAFixed.lengths.1 ReorderedAFixed.lengths.2.2.2 ReorderedAFixed.fits s m hz hb clean.cin ha]
    exact ReorderedAFixed.good_old base hc O hO s _ hf
  have middleEq := A161Low4FixedFold.cert100.middle_eq ReorderedAFixed.hs (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g)
    A161Low4FixedFold.checked.out (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) s m zeroU offHs
  have knownEq := AKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
  have goodKnown : WReady ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
      (regValue ReorderedAFixed.src s.basis)
      (middleState (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) KnownAMidStaged.body s m) := by
    rw [knownEq, middleEq]; exact goodOriginal
  have buildFrame := ReorderedAPlain.build_triple ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
    ReorderedAFixed.lengths.1 ReorderedAFixed.lengths.2.2.2 ReorderedAFixed.fits s.basis hz hb clean.cin s
    (m.take (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src))) ⟨ha, fun _ _ => rfl⟩
  have flag : (run (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
      (m.take (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src))) s).basis 4762 = false :=
    (buildFrame.2.2 4762 (by decide +kernel)).trans clean.modFlag
  have plainNew := core_plainA s m hz hb clean.cin ha zeroOld goodKnown flag
  have midEq : run KnownAMidStaged.body (m.drop (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)))
      (run (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) m s) =
      run A161Low4FixedFold.checked.out (m.drop (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)))
      (run (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) m s) := by
    simpa only [middleState, run_take] using knownEq
  have ctxt := ReorderedKnownA.context_eq (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
    A161Low4FixedFold.checked.out KnownAMidStaged.body (ReorderedAPlain.unbuild ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
    s m AKnownMiddleResearch.measurements midEq
  have middleReplace := A161Low4FixedFold.cert100.surround_eq ReorderedAFixed.hs (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g)
    A161Low4FixedFold.checked.out (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
    (ReorderedAPlain.unbuild ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) s m zeroU offHs
  exact ReorderedAFixed.transport _ s _ _ (plainNew.trans (ctxt.trans middleReplace)) (ReorderedAFixed.plain_frame base hc O hO s m hf)

private theorem keepA_cached_wires : wires rawFA ⊆ A109Research.domain.toFinset ∪ keepA.toFinset :=
  (ReorderedSupport.cached 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
    (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
    (by rw [A109Research.raw_lengths.2.2]; decide)
    (by rw [A109Research.raw_lengths.1, A109Research.raw_lengths.2.1])
    (by rw [A109Research.raw_lengths.2.1, A109Research.raw_lengths.2.2])).1

private theorem keepA_consumed_wires :
    wires (ReorderedConsumedSub.consumed 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin) ⊆
      A109Research.domain.toFinset ∪ keepA.toFinset :=
  ReorderedSupport.consumed 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
    (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
    (by rw [A109Research.raw_lengths.2.2]; decide)
    (by rw [A109Research.raw_lengths.1, A109Research.raw_lengths.2.1])
    (by rw [A109Research.raw_lengths.2.1, A109Research.raw_lengths.2.2])

theorem loopPCA_off (h : Wire) (hh : h ∈ ReorderedAFixed.hosts) (hk : h ∉ keepA) : h ∉ wires loopPCA := by
  have hA : h ∈ A109Research.hosts := List.mem_append.mpr (Or.inl hh)
  have hb : h ∉ wires (ReorderedAPlain.build ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedAFixed.off_plain h hh).1
  rw [A109Research.plain_split] at hb
  simp only [wires_append, Finset.mem_union, not_or] at hb
  have ht : h ∉ wires (ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedAFixed.off_plain h hh).2
  rw [A109Research.unbuild_split] at ht
  simp only [wires_append, Finset.mem_union, not_or] at ht
  have clearOff : h ∉ wires A109LowEraseResearch.clear := by
    rw [StairSqLoopA.clear_wires]; intro bad
    exact A109Research.old_away h hh ((by decide : ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire) ⊆ A109Research.ports) (List.mem_toFinset.mp bad))
  have out : h ∉ A109Research.domain.toFinset ∪ keepA.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]; exact ⟨A109Research.geometry.2.2 h hA, hk⟩
  simp only [loopPCA, restA, newIA, wires_append, Finset.mem_union, not_or, and_assoc]
  exact ⟨fun bad => hb.1 (SignAHeadSupport.support bad), clearOff, fun bad => out (keepA_cached_wires bad),
    A109Research.top_off h hA, A109Research.middle_fresh h hA, A109Research.preInv_off h hA,
    fun bad => out (keepA_consumed_wires bad), clearOff, ht.2⟩

theorem loopPCA_support : wires loopPCA ⊆ A109Research.S := by
  have hh : wires SignAHead.head ⊆ A109Research.S := by
    apply Finset.Subset.trans ?_ A109Research.old_prefix_support
    rw [A109Research.oldPrefix, wires_append]
    exact Finset.subset_union_left
  have ks : A109Research.domain.toFinset ∪ keepA.toFinset ⊆ A109Research.S := by
    intro q hq; apply A109Research.raw_domain_in
    simp only [Finset.mem_union, List.mem_toFinset] at hq ⊢
    rcases hq with h | h; exact Or.inl h; exact Or.inr (keepA_sub q h)
  simp only [loopPCA, restA, newIA, wires_append, Finset.union_subset_iff]
  exact ⟨hh,
    ⟨⟨⟨⟨⟨⟨A109Research.clear_support, keepA_cached_wires.trans ks⟩, A109Research.endpoint_support.1⟩,
      A109Research.middle_support⟩, ⟨A109Research.endpoint_support.2.1, keepA_consumed_wires.trans ks⟩⟩,
      A109Research.clear_support⟩, A109Research.endpoint_support.2.2⟩⟩

theorem loopPCA_physical : GatePhysical loopPCA := by
  have f := ReorderedPhysical.cached 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
    (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
    (by rw [A109Research.raw_lengths.2.2]; decide)
    A109Research.raw_nd (fun q hq bad => A109Research.geometry.2.2 q (keepA_sub q hq) (A109Research.c_in q bad))
  have n := notRegister_physical A109Research.ys
  simp only [loopPCA, restA, newIA, ReorderedConsumedSub.consumed, gatePhysical_append]
  exact ⟨SignAHeadResources.physical,
    ⟨⟨⟨⟨⟨⟨A109LowEraseResearch.physical, f.1⟩, A109Research.endpoint_physical.2.1⟩,
      AAliasesResearch.physical⟩, ⟨A109Research.endpoint_physical.2.2.1, ⟨⟨n, f.2⟩, n⟩⟩⟩,
      A109LowEraseResearch.physical⟩, A109Research.endpoint_physical.2.2.2⟩⟩

theorem loopA_pairs_free : ∀ ab ∈ StairSqLoopA.pairs hs, ab.2 ∉ wires loopPCA := by
  intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
  apply loopPCA_off _ (StairSqLoopA.hosts_of_hs _ (StairSqLoopA.holes_geometry44.2.2 y hy))
  have h := List.idxOf_lt_length_of_mem hy; rw [StairSqLoopA.hostDomain_length44] at h
  exact keepA_geometry.2.2.2.2.1 _ h

theorem loopA_support : wires loopA ⊆ A109Research.S := by
  intro q hq
  have sub := hostRename_support (StairSqLoopA.pairs hs) loopPCA (StairSqLoopA.pairs_nodup44 hs (List.Sublist.refl _)) loopA_pairs_free hq
  rcases Finset.mem_union.mp sub with h | h
  · exact loopPCA_support (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopA.pairs_snd] at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact A109Research.raw_domain_in (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (StairSqLoopA.hosts_of_hs _ (StairSqLoopA.holes_geometry44.2.2 y hy))))))

theorem loopA_avoids_hs : ∀ q ∈ hs, q ∉ wires loopA := by
  intro q hq
  have h := hostRename_avoids (StairSqLoopA.pairs hs) loopPCA (StairSqLoopA.pairs_nodup44 hs (List.Sublist.refl _)) loopA_pairs_free
  rw [StairSqLoopA.pairs_fst] at h; exact h q hq

theorem loopA_avoids_workTA : ∀ q ∈ workTA, q ∉ wires loopA := by
  intro q hq bad
  have sub := hostRename_support (StairSqLoopA.pairs hs) loopPCA (StairSqLoopA.pairs_nodup44 hs (List.Sublist.refl _)) loopA_pairs_free bad
  rcases Finset.mem_union.mp sub with h | h
  · have hm : ∀ x ∈ workTA, x ∈ ReorderedAFixed.hosts := by rw [workTA_lit, hostsAFix_fast]; decide +kernel
    exact loopPCA_off q (hm q hq) (keepA_geometry.2.2.2.1 q hq) (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopA.pairs_snd] at h
    have dis : ∀ x ∈ workTA, x ∉ hs.map StairSqLoopA.hostOf := by simp only [workTA_lit, StairSqLoopA.hostOf, show StairSqLoopA.hostDomain = hs from rfl, hs_lit, hsA_fast]; decide +kernel
    exact dis q hq (List.mem_toFinset.mp h)

theorem loopA_counts :
    toffoliCount loopA = toffoliCount A109SignResearch.loop + 79 ∧
    measurementCount loopA = measurementCount A109SignResearch.loop := by
  have hr := hostRename_counts (StairSqLoopA.pairs hs) loopPCA
  have rel : toffoliCount loopPCA + 33 = toffoliCount StairSqLoopA.loopNC ∧
      measurementCount loopPCA = measurementCount StairSqLoopA.loopNC := by
    have cb := ReorderedGenericCache.count_balance 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide) (by rw [A109Research.raw_lengths.2.2]; decide)
    rw [loopPCA, restA, rawFA, newIA, StairSqLoopA.loopNC, StairSqLoopA.suffixNC,
      A109Research.I, A109Research.rawI, A109Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [toffoliCount_append, measurementCount_append]
    exact ⟨by omega, by omega⟩
  have nc := StairSqLoopA.loopNC_counts
  rw [loopA, hr.1, hr.2]
  exact ⟨by omega, by omega⟩

theorem loopA_slots : Challenge.gateSlots loopA = Challenge.gateSlots A109SignResearch.loop + 231 := by
  have hr := hostRename_slots (StairSqLoopA.pairs hs) loopPCA
  have rel : Challenge.gateSlots loopPCA + 99 = Challenge.gateSlots StairSqLoopA.loopNC := by
    have sc := ReorderedSlots.cache 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide) keepA_geometry.2.1
    rw [loopPCA, restA, rawFA, newIA, StairSqLoopA.loopNC, StairSqLoopA.suffixNC,
      A109Research.I, A109Research.rawI, A109Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [Challenge.gateSlots_append]
    omega
  have nc := StairSqLoopA.loopNC_slots
  rw [loopA, hr]
  omega

theorem loopA_frame : A109SignResearch.DirectLoopFrame loopA := by
  have pcFrame : A109SignResearch.DirectLoopFrame loopPCA := by
    intro base hc hsum hV hP hd O hO s m hf
    have clean := ReorderedAFixed.L.squareFrame_clean ReorderedAFixed.hn base s.basis O hf hc
    have hz : ∀ u ∈ ReorderedAFixed.pad, s.basis u = false := by
      intro u hu; rcases accZ_mem ReorderedAFixed.L u ((FullPadDevelop.pad_sublist ReorderedAFixed.L).subset hu) with hu' | hu'
      · exact (regValue_zero _ _).mp clean.pad u hu'
      · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu')
    have hb : ∀ u ∈ ReorderedAFixed.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
    have ha : regValue ReorderedAFixed.acc s.basis = 0 := A161Low4Ghost.ghostAcc_zero ReorderedAFixed.L s.basis clean
    have hhead : ∀ a b : List Bool, run SignAHead.head a s = run (ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) b s :=
      fun a b => ReorderedFrameUnique.program_eq ReorderedAFixed.acc s.basis 0 ((2 ^ 138 - 48 * regValue ReorderedAFixed.src s.basis) % 2 ^ 138) _ _
        (SignAHead.frame s.basis hz hb clean.cin)
        (ReorderedAHead.head_triple ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src ReorderedAFixed.lengths.1 ReorderedAFixed.lengths.2.2.2.le ReorderedAFixed.fits s.basis hz hb clean.cin)
        s a b ⟨ha, fun _ _ => rfl⟩
    have eq := SignRetape.replace SignAHead.head (ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) restA s m hhead
    have hheadEq : A109Research.head = ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src := rfl
    have hcoreEq : coreA = ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src ++ restA := by
      rw [coreA, newFA, restA, hheadEq]
      have g (A B C D E F G H : Program) : (((A ++ B ++ C ++ D) ++ E ++ F) ++ (G ++ H)) = A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H) := by simp only [List.append_assoc]
      exact g _ _ _ _ _ _ _ _
    have eq' : run loopPCA m s = run coreA (SignRetape.tape SignAHead.head (ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) m) s := by
      rw [loopPCA, hcoreEq]; exact eq
    exact ReorderedAFixed.transport _ s _ _ eq' (coreA_frame base hc hsum hV hP hd O hO s _ hf)
  intro base hc hsum hV hP hd O hO s m hf
  have r := pcFrame base hc hsum hV hP hd O hO s m hf
  have hEq : run loopA m s = run loopPCA m s := by
    apply hostRename_run_eq (StairSqLoopA.pairs hs) loopPCA s m
    · intro ab hab; obtain ⟨y, hy, hyab⟩ := List.mem_map.mp hab
      have hfst : ab.1 = y := by rw [← hyab]
      rw [hfst]
      have hg := StairSqLoopA.holes_geometry44.2.1 y hy
      exact (hf.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact (hf.2 _ (A161Low4FixedFold.hostClean base hc hd _ (StairSqLoopA.holes_geometry44.2.2 y hy)).1).trans
        (A161Low4FixedFold.hostClean base hc hd _ (StairSqLoopA.holes_geometry44.2.2 y hy)).2
    · intro ab hab
      obtain ⟨y, hy, e⟩ := List.mem_map.mp hab
      have first : ab.1 = y := by rw [← e]
      rw [first]
      have hg := StairSqLoopA.holes_geometry44.2.1 y hy
      exact (r.2.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · exact loopA_pairs_free
  rw [hEq]; exact r

theorem bodyA_wires_plain : wires bodyA ⊆ wires bodyAPlain ∪ (K0.core.pad.take 32).toFinset := by
  have sp1 := directFold_rename_support foldPairsA (negP K0) (negP_count K0) foldPairsA_geom.1 (fun ab hab => (foldPairsA_geom.2.2.2.1 ab hab).2.2.1)
  have sp2 := directFold_rename_support foldPairsA (rot128F K0) (rot128F_count K0) foldPairsA_geom.1 (fun ab hab => (foldPairsA_geom.2.2.2.1 ab hab).2.2.1)
  rw [foldPairsA_geom.2.2.1] at sp1 sp2
  intro q hq
  simp only [bodyA, wires_append, Finset.mem_union] at hq
  rcases hq with (b | b | b) | b
  · rcases Finset.mem_union.mp (sp1 b) with h | h
    · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, wires_append, Finset.mem_union]; left; left; exact (Finset.mem_sdiff.mp h).1)
    · exact Finset.mem_union_right _ h
  · rcases Finset.mem_union.mp (sp2 b) with h | h
    · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, wires_append, Finset.mem_union]; left; right; left; exact (Finset.mem_sdiff.mp h).1)
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, wires_append, Finset.mem_union]; left; right; right; exact b)
  · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, wires_append, Finset.mem_union]; right; exact b)

theorem bodyA_ok : BodyAOK bodyA := by
  have s0 := A109SignResearch.direct_body_support_S loopA loopA_support
  have e0 := A109SignResearch.direct_body_eU_free_S loopA loopA_support
  refine ⟨?_, ?_, ?_⟩
  · intro q hq; rcases Finset.mem_union.mp (bodyA_wires_plain hq) with h | h
    · exact s0 h
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsA_geom.2.2.2.2 q (by rw [foldPairsA_geom.2.2.1]; exact List.mem_toFinset.mp h)).2.2.1))
  · intro bad; rcases Finset.mem_union.mp (bodyA_wires_plain bad) with h | h
    · exact e0 h
    · exact (foldPairsA_geom.2.2.2.2 _ (by rw [foldPairsA_geom.2.2.1]; exact List.mem_toFinset.mp h)).2.1 rfl
  · intro base M hM hP hc hsum O hO hg hd s m hf
    have rawRef := A109SignResearch.direct_body_frame loopA loopA_frame base M hM hP hc hsum O hO hg hd s m hf
    have views := accA_views K0 hwK base M hM hP
    have hv1 : K0.MeasuredFoldView base (negP K0) := views (.inl (negP K0)) (by simp [accAMix])
    have hv2 : K0.MeasuredFoldView base (rot128F K0) := views (.inl (rot128F K0)) (by simp [accAMix])
    have mc1 : measurementCount dF1A = measurementCount (directFoldQTq K0 (negP K0)) := (hostRename_counts foldPairsA (directFoldQTq K0 (negP K0))).2
    have mc2 : measurementCount dF2A = measurementCount (directFoldQTq K0 (rot128F K0)) := (hostRename_counts foldPairsA (directFoldQTq K0 (rot128F K0))).2
    have eq1 : run dF1A m s = run (directFoldQTq K0 (negP K0)) m s :=
      directFold_rename_run foldPairsA (negP K0) (negP_count K0) (negP_length K0 hwK) rfl rfl
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).1, (foldPairsA_geom.2.2.2.1 ab hab).2.1⟩)
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).2.2.1, (foldPairsA_geom.2.2.2.1 ab hab).2.2.2.1⟩)
        base hv1 hc O hO s m hf
    have hn := (List.nodup_cons.mp controlND).2
    have f1 := directFoldQ_frameTq K0 hwK hn base (negP K0) hv1 rfl hc (negP_length K0 hwK) rfl O hO s m hf
    have eq2 : run dF2A (m.drop (measurementCount (directFoldQTq K0 (negP K0)))) (run (directFoldQTq K0 (negP K0)) m s) =
        run (directFoldQTq K0 (rot128F K0)) (m.drop (measurementCount (directFoldQTq K0 (negP K0)))) (run (directFoldQTq K0 (negP K0)) m s) :=
      directFold_rename_run foldPairsA (rot128F K0) (rot128F_count K0) (rot128F_length K0 hwK) rfl rfl
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).1, (foldPairsA_geom.2.2.2.1 ab hab).2.1⟩)
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).2.2.1, (foldPairsA_geom.2.2.2.1 ab hab).2.2.2.1⟩)
        base hv2 hc _ (Nat.mod_lt _ (by norm_num [SquareReduction.p, SquareReduction.B, SquareReduction.c])) _ _ f1.2
    have bodyEq : run bodyA m s = run bodyAPlain m s := by
      simp only [bodyA, bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
        ControlledBorrowResearch.run_cat, measurementCount_append, mc1, mc2]
      rw [eq1, eq2]
    rw [bodyEq]; exact rawRef

theorem bodyA_avoids_workTA : ∀ q ∈ workTA, q ∉ wires bodyA := by
  intro q hq bad
  have hn := (List.nodup_cons.mp controlND).2
  have a1 := hostRename_avoids foldPairsA (directFoldQTq K0 (negP K0)) foldPairsA_geom.1
    (fun ab hab => directFoldQ_free K0 hn (negP K0) (negP_count K0) ab.2 (by simp [directFree, (foldPairsA_geom.2.2.2.1 ab hab).2.2.1]))
  have a2 := hostRename_avoids foldPairsA (directFoldQTq K0 (rot128F K0)) foldPairsA_geom.1
    (fun ab hab => directFoldQ_free K0 hn (rot128F K0) (rot128F_count K0) ab.2 (by simp [directFree, (foldPairsA_geom.2.2.2.1 ab hab).2.2.1]))
  rw [foldPairsA_geom.2.1] at a1 a2
  simp only [bodyA, wires_append, Finset.mem_union] at bad
  rcases bad with (b | b | b) | b
  · exact a1 q hq b
  · exact a2 q hq b
  · exact loopA_avoids_workTA q hq b
  · exact (by rw [workTA_lit, K0_eq]; decide +kernel : ∀ x ∈ workTA, x ≠ K0.core.cin) q hq (Finset.mem_singleton.mp (padding_wires 7 K0.core.cin b))

theorem bodyA_avoids_hs : ∀ q ∈ hs, q ∉ wires bodyA := by
  intro q hq bad
  rcases Finset.mem_union.mp (bodyA_wires_plain bad) with h | h
  · exact A109SignResearch.direct_body_holes loopA hs (fun x hx => (StairSqLoopA.holes_geometry44.2.1 x hx).1) loopA_avoids_hs q hq h
  · exact (foldPairsA_geom.2.2.2.2 q (by rw [foldPairsA_geom.2.2.1]; exact List.mem_toFinset.mp h)).1 hq

theorem bodyA_physical : GatePhysical bodyA := by
  have p0 := A109SignResearch.direct_body_physical loopA (hostRename_physical _ _ loopPCA_physical)
  simp only [A109SignResearch.directBody, A109SignResearch.directRawBody, gatePhysical_append] at p0
  simp only [bodyA, dF1A, dF2A, gatePhysical_append]
  exact ⟨⟨hostRename_physical _ _ p0.1.1, ⟨hostRename_physical _ _ p0.1.2.1, p0.1.2.2⟩⟩, p0.2⟩

theorem bodyA_counts :
    toffoliCount bodyA = toffoliCount A109SignResearch.body + 79 ∧
    measurementCount bodyA = measurementCount A109SignResearch.body := by
  have c0 := A109SignResearch.direct_body_counts loopA
  have cl := loopA_counts
  have r1 := hostRename_counts foldPairsA (directFoldQTq K0 (negP K0))
  have r2 := hostRename_counts foldPairsA (directFoldQTq K0 (rot128F K0))
  have eqT : toffoliCount bodyA = toffoliCount (A109SignResearch.directBody loopA) := by
    simp only [bodyA, dF1A, dF2A, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
      toffoliCount_append, r1.1, r2.1]
  have eqM : measurementCount bodyA = measurementCount (A109SignResearch.directBody loopA) := by
    simp only [bodyA, dF1A, dF2A, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
      measurementCount_append, r1.2, r2.2]
  rw [eqT, eqM]
  exact ⟨by omega, by omega⟩

theorem bodyA_slots : Challenge.gateSlots bodyA + 793 = Challenge.gateSlots A109SignResearch.body := by
  have s0 := A109SignResearch.direct_body_slots loopA
  have sl := loopA_slots
  have r1 := hostRename_slots foldPairsA (directFoldQTq K0 (negP K0))
  have r2 := hostRename_slots foldPairsA (directFoldQTq K0 (rot128F K0))
  have eqS : Challenge.gateSlots bodyA = Challenge.gateSlots (A109SignResearch.directBody loopA) := by
    simp only [bodyA, dF1A, dF2A, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
      Challenge.gateSlots_append, r1, r2]
  rw [eqS]
  omega

theorem bodyAPlain_coarse :
    wires bodyAPlain ⊆ insert D0 (G0 :: K0.wires).toFinset :=
  A109SignResearch.direct_body_coarse_S loopA loopA_support

theorem bodyAPlain_fine :
    wires bodyAPlain ⊆ insert D0 (wires (InverseCarryDevelop.hostedADual K0
      (LowZero18Square.foldPerm K0 E0) G0)) :=
  A109SignResearch.direct_body_fine_S loopA loopA_support

end BodyA

/-! ## Branch B body (`keepB` = 19 carries, `efSwapB` = 20 swaps, avoids `workTB`, `hs`, `normFlag`) -/

section BodyB
open ControlLoan1589BFFold ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical LocalRebuild.improved directFoldQTq ControlLoan1589BFFold.eAddLo ControlLoan1589BFFold.eSubK ParkCarryDevelop.program ParkCarry10Develop.rebuild

private theorem lb_eq_K0 : StairSqBodyB.LB = K0 := rfl
private theorem cb_eq_G0 : StairSqBodyB.cB = G0 := rfl

def keepB : List Wire := (B95Research.keepK.filter (fun q => !workTB.contains q)).take 19

theorem keepB_geometry : keepB.Nodup ∧ keepB.length = 19 ∧
    (∀ q ∈ keepB, q ∈ B95Research.hosts) ∧
    (∀ q ∈ workTB, q ∉ keepB) ∧
    (∀ i, i < 44 → LowAccCarryDevelop.hosts88.getD i 0 ∉ keepB) ∧
    (4761 : Wire) ∉ keepB ∧
    (∀ q ∈ keepB, q ∈ allowedWires) := by
  have hall : ∀ q ∈ keepB, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [keepB, keepKB_fast, workTB_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [keepB, keepKB_fast, workTB_lit, hs_lit]; decide +kernel))
  have hr : keepB.Nodup ∧ keepB.length = 19 ∧
      (∀ q ∈ keepB, q ∈ B95Research.hosts) ∧
      (∀ q ∈ workTB, q ∉ keepB) ∧
      (∀ i, i < 44 → LowAccCarryDevelop.hosts88.getD i 0 ∉ keepB) ∧
      (4761 : Wire) ∉ keepB := by rw [keepB, keepKB_fast, hostsB95_fast, hosts88_fast, workTB_lit]; decide +kernel
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, hall⟩

def rawFB : Program := ReorderedGenericCache.cachedAdd 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
def newFB : Program := B95Research.head ++ B95LowEraseResearch.clear ++ rawFB ++ B95Research.top
def newIB : Program := B95Research.preInv ++ ReorderedConsumedSub.consumed 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
def coreB : Program := (newFB ++ B95Research.M ++ newIB) ++ (B95LowEraseResearch.clear ++ B95Research.tail)
def restB : Program := B95LowEraseResearch.clear ++ rawFB ++ B95Research.top ++ B95Research.M ++ newIB ++ B95LowEraseResearch.clear ++ B95Research.tail
def loopPCB : Program := KnownBHeadResearch.output ++ restB
def loopB : Program := hostRename (StairSqLoopB.pairs hs) loopPCB
def foldPairsB : List (Wire × Wire) := (workTB.take 31).zip (K0.core.pad.take 31)
def dF1B : Program := hostRename foldPairsB (directFoldQTq K0 (negP K0))
def dF2B : Program := hostRename foldPairsB (directFoldQTq K0 (rot128F K0))
def efoldB : Program := hostRename efSwapB StairSquareBEFoldK.efold
def bodyB : Program :=
  StairSquareBBody.bodyG K0 dF1B dF2B loopB efoldB LocalRebuild.improved ++
    ReorderedRecordPadding.program 4 K0.core.cin

theorem foldPairsB_geom :
    (holesOf foldPairsB ++ hostsOf foldPairsB).Nodup ∧
    holesOf foldPairsB = workTB.take 31 ∧
    hostsOf foldPairsB = K0.core.pad.take 31 ∧
    (∀ ab ∈ foldPairsB, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out ∧ ab.2 ∈ allowedWires) ∧
    (∀ q ∈ hostsOf foldPairsB, q ∉ hs ∧ q ≠ K0.core.normFlag ∧ q ∈ K0.wires ∧ q ∈ allowedWires) := by
  have hall : ∀ q ∈ hostsOf foldPairsB, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsB, workTB_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [foldPairsB, workTB_lit, K0_eq, hs_lit]; decide +kernel))
  have hK : ∀ q ∈ hostsOf foldPairsB, q ∈ K0.wires :=
    StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsB, workTB_lit, K0_eq]; decide +kernel)
  have hr : (holesOf foldPairsB ++ hostsOf foldPairsB).Nodup ∧
      holesOf foldPairsB = workTB.take 31 ∧
      hostsOf foldPairsB = K0.core.pad.take 31 ∧
      (∀ ab ∈ foldPairsB, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out) ∧
      (∀ q ∈ hostsOf foldPairsB, q ∉ hs ∧ q ≠ K0.core.normFlag) := by
    rw [foldPairsB, workTB_lit, K0_eq, hs_lit]; decide +kernel
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_, ?_⟩
  · intro ab hab; have h := hr.2.2.2.1 ab hab
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hall ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩)⟩
  · intro q hq; have h := hr.2.2.2.2 q hq
    exact ⟨h.1, h.2, hK q hq, hall q hq⟩

private theorem keepB_sub (q : Wire) (hq : q ∈ keepB) : q ∈ B95Research.hosts := keepB_geometry.2.2.1 q hq

private theorem core_plainB (s : State) (m : List Bool)
    (hz : ∀ q ∈ ReorderedBPrefixResearch.pad, s.basis q = false) (hb : ∀ q ∈ ReorderedBPrefixResearch.bank, s.basis q = false)
    (hi : s.basis ReorderedBPrefixResearch.cin = false) (ha : regValue ReorderedBPrefixResearch.acc s.basis = 0)
    (zero : ∀ q ∈ ReorderedBSupportResearch.hosts, s.basis q = false)
    (after : WReady ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src
      (regValue ReorderedBPrefixResearch.src s.basis) (middleState B95Research.oldF B95Research.oldM s m))
    (flag : (run B95Research.oldF (m.take (measurementCount B95Research.oldF)) s).basis 4762 = false) :
    run coreB m s = run (B95Research.oldF ++ B95Research.oldM ++
      ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) m s := by
  let H := regValue ReorderedBPrefixResearch.src s.basis
  let vs := ReorderedCacheBits.values 4 19 H (976 * H / 1024)
  have fwdM : measurementCount newFB = measurementCount B95Research.F := by
    have h := (ReorderedGenericCache.count_balance 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide)).2.1
    simp only [newFB, rawFB, B95Research.F, B95Research.rawF, measurementCount_append]; rw [h]
  have invM : measurementCount newIB = measurementCount B95Research.I := by
    have h := ReorderedConsumedSub.measurement_eq 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide)
    simp only [newIB, B95Research.I, B95Research.rawI, measurementCount_append]; rw [h]
  have fwdVal : (((B95Research.cs.drop 4).take 19).map (run (carryPrefix (4 + 19) B95Research.xs B95Research.ys B95Research.cs ReorderedBPrefixResearch.cin) []
      (run (B95Research.head ++ B95LowEraseResearch.clear)
        ((m.take (measurementCount B95Research.F)).take (measurementCount (B95Research.head ++ B95LowEraseResearch.clear))) s)).basis) = vs := by
    let m0 := (m.take (measurementCount B95Research.F)).take (measurementCount (B95Research.head ++ B95LowEraseResearch.clear))
    let u := run B95Research.head m0 s
    let t := run (B95Research.head ++ B95LowEraseResearch.clear) m0 s
    have te : t = B95LowEraseResearch.erase u := B95Research.prefix_erased s m0 hz hb hi ha
    have hH : H < 2 ^ 128 := by simpa only [H, ReorderedBPrefixResearch.source_length] using regValue_lt ReorderedBPrefixResearch.src s.basis
    have ready := ReorderedHeadArithmeticResearch.ready ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank
      ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits s m0 hz hb hi ha
    have eb (q : Wire) (hq : q ∈ B95Research.domain) : t.basis q = u.basis q := by
      rw [te]; exact B95LowEraseResearch.bit_same _ q (B95Research.domain_away_low q hq)
    have er (r : List Wire) (sub : ∀ q ∈ r, q ∈ B95Research.domain) : regValue r t.basis = regValue r u.basis :=
      regValue_congr _ _ _ (fun q hq => eb q (sub q hq))
    exact ReorderedCacheBits.forward_values 4 19 H (((2 ^ 138 - 48 * H) % 2 ^ 138) / 1024) (976 * H / 1024)
      B95Research.xs B95Research.ys B95Research.cs ReorderedBPrefixResearch.cin t
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide) B95Research.raw_nd
      (fun q hq => (eb q (B95Research.c_in q hq)).trans (ready.1 q hq))
      ((eb _ B95Research.cin_in).trans ready.2.1)
      ((er _ B95Research.x_in).trans ready.2.2.1)
      ((er _ B95Research.y_in).trans ready.2.2.2)
      (fun j hj => by simpa only [show 128 + 10 = 138 by decide] using ReorderedCacheArithmetic.high_add_low 128 (4 + j + 1) H (by omega) hH)
  have forward : run newFB (m.take (measurementCount B95Research.F)) s =
      scatterState keepB vs (run B95Research.F (m.take (measurementCount B95Research.F)) s) := by
    have h := CacheBetweenFrameResearch.forward (B95Research.head ++ B95LowEraseResearch.clear) B95Research.top
      19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide) keepB_geometry.1
      (fun q hq bad => B95Research.geometry.2.2 q (keepB_sub q hq) (by clear * - bad; simp only [B95Research.domain, List.mem_cons, List.mem_append] at bad ⊢; tauto))
      (fun q hq => B95Research.rawF_off q (keepB_sub q hq)) (fun q hq => B95Research.top_off q (keepB_sub q hq))
      s (m.take (measurementCount B95Research.F))
      (fun q hq => B95Research.prefix_zero s _ hz hb hi ha zero q (keepB_sub q hq))
    rw [fwdVal] at h; exact h
  have mid := B95Research.middle_erased s m hz hb hi ha after flag
  have cacheEq : run (newFB ++ B95Research.M ++ newIB) m s = run (B95Research.F ++ B95Research.M ++ B95Research.I) m s := by
    apply CacheFromCleanForwardResearch.equivalent B95Research.F newFB B95Research.M B95Research.I newIB keepB vs
      fwdM (fun q hq => B95Research.middle_fresh q (keepB_sub q hq))
      (fun q hq => B95Research.I_off q (keepB_sub q hq)) keepB_geometry.1 s m
      (fun q hq => B95Research.forward_zero s _ hz hb hi ha zero q (keepB_sub q hq)) forward
    rw [mid]
    let ms := middleState B95Research.oldF B95Research.oldM s m
    let mr := m.drop (measurementCount B95Research.F + measurementCount B95Research.M)
    let t := scatterState keepB vs (B95LowEraseResearch.erase ms)
    have comm : run B95Research.preInv mr t = scatterState keepB vs (B95LowEraseResearch.erase (run B95Research.preInv mr ms)) := by
      rw [show t = scatterState keepB vs (B95LowEraseResearch.erase ms) from rfl,
        run_scatter B95Research.preInv keepB vs _ _ (fun q hq => B95Research.preInv_off q (keepB_sub q hq)),
        B95LowEraseResearch.commute B95Research.preInv mr ms (fun q hq => B95Research.preInv_off q (B95Research.low_hosts q hq))]
    have bits (q : Wire) (hq : q ∈ B95Research.domain) : (run B95Research.preInv mr t).basis q = (run B95Research.preInv mr ms).basis q := by
      rw [comm, scatter_outside keepB vs _ q (fun bad => B95Research.geometry.2.2 q (keepB_sub q bad) hq)]
      exact B95LowEraseResearch.bit_same _ q (B95Research.domain_away_low q hq)
    have regs (r : List Wire) (sub : ∀ q ∈ r, q ∈ B95Research.domain) :
        regValue r (run B95Research.preInv mr t).basis = regValue r (run B95Research.preInv mr ms).basis :=
      regValue_congr _ _ _ (fun q hq => bits q (sub q hq))
    have rr := B95Research.pre_raw_ready H ms mr after
    have saved : keepB.map t.basis = vs := scatter_saved_map keepB vs _ keepB_geometry.1
      (by simp only [vs, ReorderedCacheBits.values, List.length_map, keepB_geometry.2.1, List.length_range])
    have same : keepB.map (run B95Research.preInv mr t).basis = keepB.map t.basis :=
      List.map_congr_left (fun q hq => run_preserves_outside B95Research.preInv mr t q (B95Research.preInv_off q (keepB_sub q hq)))
    simp only [newIB, B95Research.I, B95Research.rawI, ControlledBorrowResearch.run_cat]
    exact ReorderedConsumedSub.frame 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide)
      (by rw [B95Research.raw_lengths.1, B95Research.raw_lengths.2.1])
      (by rw [B95Research.raw_lengths.2.1, B95Research.raw_lengths.2.2])
      B95Research.raw_nd keepB_geometry.1 keepB_geometry.2.1 (fun q hq => B95Research.geometry.2.2 q (keepB_sub q hq))
      (run B95Research.preInv mr t) _ (fun q hq => (bits q (B95Research.c_in q hq)).trans (rr.1 q hq))
      ((bits _ B95Research.cin_in).trans rr.2.1) H (976 * H / 1024)
      ((regs _ B95Research.x_in).trans rr.2.2.1) ((regs _ B95Research.y_in).trans rr.2.2.2) (same.trans saved)
  have eq := ClearContextResearch.append_at (newFB ++ B95Research.M ++ newIB)
    (B95Research.F ++ B95Research.M ++ B95Research.I) (B95LowEraseResearch.clear ++ B95Research.tail) s m
    (by simp only [measurementCount_append, fwdM, invM]) cacheEq
  have shape : (B95Research.F ++ B95Research.M ++ B95Research.I) ++ (B95LowEraseResearch.clear ++ B95Research.tail) =
      B95Research.F ++ B95Research.M ++ (B95Research.I ++ B95LowEraseResearch.clear ++ B95Research.tail) := by
    have g (A B C D E : Program) : (A ++ B ++ C) ++ (D ++ E) = A ++ B ++ (C ++ D ++ E) := by simp only [List.append_assoc]
    exact g _ _ _ _ _
  exact eq.trans ((congrArg (fun P => run P m s) shape).trans (B95Research.plain_loop s m hz hb hi ha after flag))

private theorem keepB_cached_wires : wires rawFB ⊆ B95Research.domain.toFinset ∪ keepB.toFinset :=
  (ReorderedSupport.cached 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
    (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
    (by rw [B95Research.raw_lengths.2.2]; decide)
    (by rw [B95Research.raw_lengths.1, B95Research.raw_lengths.2.1])
    (by rw [B95Research.raw_lengths.2.1, B95Research.raw_lengths.2.2])).1

private theorem keepB_consumed_wires :
    wires (ReorderedConsumedSub.consumed 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin) ⊆
      B95Research.domain.toFinset ∪ keepB.toFinset :=
  ReorderedSupport.consumed 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
    (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
    (by rw [B95Research.raw_lengths.2.2]; decide)
    (by rw [B95Research.raw_lengths.1, B95Research.raw_lengths.2.1])
    (by rw [B95Research.raw_lengths.2.1, B95Research.raw_lengths.2.2])

theorem loopPCB_off (h : Wire) (hh : h ∈ ReorderedBSupportResearch.hosts) (hk : h ∉ keepB) : h ∉ wires loopPCB := by
  have hA : h ∈ B95Research.hosts := List.mem_append.mpr (Or.inl hh)
  have hb : h ∉ wires (ReorderedAPlain.build ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedBSupportResearch.plain_free h hh).1
  rw [B95Research.plain_split] at hb
  simp only [wires_append, Finset.mem_union, not_or] at hb
  have ht : h ∉ wires (ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedBSupportResearch.plain_free h hh).2
  rw [B95Research.unbuild_split] at ht
  simp only [wires_append, Finset.mem_union, not_or] at ht
  have clearOff : h ∉ wires B95LowEraseResearch.clear := by
    rw [StairSqLoopB.clear_wires]; intro bad
    exact B95Research.old_away h hh ((by decide : ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire) ⊆ B95Research.ports) (List.mem_toFinset.mp bad))
  have out : h ∉ B95Research.domain.toFinset ∪ keepB.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]; exact ⟨B95Research.geometry.2.2 h hA, hk⟩
  simp only [loopPCB, restB, newIB, wires_append, Finset.mem_union, not_or, and_assoc]
  exact ⟨fun bad => hb.1 (KnownBHeadResearch.support bad), clearOff, fun bad => out (keepB_cached_wires bad),
    B95Research.top_off h hA, B95Research.middle_fresh h hA, B95Research.preInv_off h hA,
    fun bad => out (keepB_consumed_wires bad), clearOff, ht.2⟩

theorem loopPCB_support : wires loopPCB ⊆ B95Research.S := by
  have ks : B95Research.domain.toFinset ∪ keepB.toFinset ⊆ B95Research.S := by
    intro q hq; apply B95Research.raw_domain_in
    simp only [Finset.mem_union, List.mem_toFinset] at hq ⊢
    rcases hq with h | h; exact Or.inl h; exact Or.inr (keepB_sub q h)
  simp only [loopPCB, restB, newIB, wires_append, Finset.union_subset_iff]
  exact ⟨KnownBHeadResearch.support.trans B95Research.endpoint_support.1,
    ⟨⟨⟨⟨⟨⟨B95Research.clear_support, keepB_cached_wires.trans ks⟩, B95Research.endpoint_support.2.1⟩,
      B95Research.middle_support⟩, ⟨B95Research.endpoint_support.2.2.1, keepB_consumed_wires.trans ks⟩⟩,
      B95Research.clear_support⟩, B95Research.endpoint_support.2.2.2⟩⟩

theorem loopPCB_physical : GatePhysical loopPCB := by
  have f := ReorderedPhysical.cached 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
    (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
    (by rw [B95Research.raw_lengths.2.2]; decide)
    B95Research.raw_nd (fun q hq bad => B95Research.geometry.2.2 q (keepB_sub q hq) (B95Research.c_in q bad))
  have n := notRegister_physical B95Research.ys
  simp only [loopPCB, restB, newIB, ReorderedConsumedSub.consumed, gatePhysical_append]
  exact ⟨KnownBHeadResearch.physical B95Research.endpoint_physical.1,
    ⟨⟨⟨⟨⟨⟨B95LowEraseResearch.physical, f.1⟩, B95Research.endpoint_physical.2.1⟩,
      B95AliasesResearch.physical⟩, ⟨B95Research.endpoint_physical.2.2.1, ⟨⟨n, f.2⟩, n⟩⟩⟩,
      B95LowEraseResearch.physical⟩, B95Research.endpoint_physical.2.2.2⟩⟩

theorem loopB_pairs_free : ∀ ab ∈ StairSqLoopB.pairs hs, ab.2 ∉ wires loopPCB := by
  intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
  apply loopPCB_off _ (StairSqLoopB.hosts_of_88 _ (StairSqLoopB.holes_geometry44.2.2 y hy))
  have h := List.idxOf_lt_length_of_mem hy; rw [StairSqLoopA.hostDomain_length44] at h
  exact keepB_geometry.2.2.2.2.1 _ h

theorem loopB_support : wires loopB ⊆ B95Research.S := by
  intro q hq
  have sub := hostRename_support (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free hq
  rcases Finset.mem_union.mp sub with h | h
  · exact loopPCB_support (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopB.pairs_snd] at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact B95Research.raw_domain_in (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (StairSqLoopB.hosts_of_88 _ (StairSqLoopB.holes_geometry44.2.2 y hy))))))

theorem loopB_avoids_hs : ∀ q ∈ hs, q ∉ wires loopB := by
  intro q hq
  have h := hostRename_avoids (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free
  rw [StairSqLoopB.pairs_fst] at h; exact h q hq

theorem loopB_avoids_workTB : ∀ q ∈ workTB, q ∉ wires loopB := by
  intro q hq bad
  by_cases hD : q = D0
  · subst hD
    have park := ParkCarry10Develop.body_support StairSqBodyB.LB LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup StairSqBodyB.cB
    have hsup := park (FullB99OptTemp.actual_subset (loopB_support bad))
    rw [lb_eq_K0, cb_eq_G0] at hsup
    exact (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (List.mem_toFinset.mp hsup)
  · have sub := hostRename_support (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free bad
    rcases Finset.mem_union.mp sub with h | h
    · have hm : ∀ x ∈ workTB, x ≠ D0 → x ∈ ReorderedBSupportResearch.hosts := by rw [workTB_lit, D0_eq, hostsBSup_fast]; decide +kernel
      exact loopPCB_off q (hm q hq hD) (keepB_geometry.2.2.2.1 q hq) (Finset.mem_sdiff.mp h).1
    · rw [StairSqLoopB.pairs_snd] at h
      have dis : ∀ x ∈ workTB, x ∉ hs.map StairSqLoopB.hostOf := by simp only [workTB_lit, StairSqLoopB.hostOf, show StairSqLoopA.hostDomain = hs from rfl, hs_lit, hosts88_fast]; decide +kernel
      exact dis q hq (List.mem_toFinset.mp h)

theorem loopB_normFlag : K0.core.normFlag ∉ wires loopB := by
  have hM := StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.middle_norm _ (List.mem_singleton_self _)
  have hb := StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.build_norm _ (List.mem_singleton_self _)
  have hu := StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.unbuild_norm _ (List.mem_singleton_self _)
  rw [B95Research.plain_split] at hb; rw [B95Research.unbuild_split] at hu
  simp only [wires_append, Finset.mem_union, not_or] at hb hu
  have clearOff : K0.core.normFlag ∉ wires B95LowEraseResearch.clear := by
    rw [StairSqLoopB.clear_wires]; intro h
    exact (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel : K0.core.normFlag ∉ ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire)) (List.mem_toFinset.mp h)
  have out : K0.core.normFlag ∉ B95Research.domain.toFinset ∪ keepB.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]
    exact ⟨fun h => hb.2.1 (by rw [B95Research.raw_wires]; exact List.mem_toFinset.mpr h), keepB_geometry.2.2.2.2.2.1⟩
  have pcNF : K0.core.normFlag ∉ wires loopPCB := by
    have hI := hu.1; simp only [B95Research.I, wires_append, Finset.mem_union, not_or] at hI
    simp only [loopPCB, restB, newIB, wires_append, Finset.mem_union, not_or, and_assoc]
    exact ⟨fun h => hb.1 (KnownBHeadResearch.support h), clearOff, fun h => out (keepB_cached_wires h),
      hb.2.2, hM, hI.1, fun h => out (keepB_consumed_wires h), clearOff, hu.2⟩
  intro bad
  have sub := hostRename_support (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free bad
  rcases Finset.mem_union.mp sub with h | h
  · exact pcNF (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopB.pairs_snd] at h
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    have hm := StairSqLoopB.holes_geometry44.2.2 y hy; rw [hyx] at hm
    exact (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel : K0.core.normFlag ∉ LowAccCarryDevelop.hosts88) hm

theorem loopB_counts :
    toffoliCount loopB = toffoliCount B95Research.loop + 79 ∧
    measurementCount loopB = measurementCount B95Research.loop := by
  have hr := hostRename_counts (StairSqLoopB.pairs hs) loopPCB
  have rel : toffoliCount loopPCB + 19 = toffoliCount StairSqLoopB.loopNC ∧
      measurementCount loopPCB = measurementCount StairSqLoopB.loopNC := by
    have cb := ReorderedGenericCache.count_balance 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide) (by rw [B95Research.raw_lengths.2.2]; decide)
    rw [loopPCB, restB, rawFB, newIB, StairSqLoopB.loopNC, StairSqLoopB.restNC,
      B95Research.I, B95Research.rawI, B95Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [toffoliCount_append, measurementCount_append]
    exact ⟨by omega, by omega⟩
  have nc := StairSqLoopB.loopNC_counts
  rw [loopB, hr.1, hr.2]
  exact ⟨by omega, by omega⟩

theorem loopB_slots : Challenge.gateSlots loopB = Challenge.gateSlots B95Research.loop + 231 := by
  have hr := hostRename_slots (StairSqLoopB.pairs hs) loopPCB
  have rel : Challenge.gateSlots loopPCB + 57 = Challenge.gateSlots StairSqLoopB.loopNC := by
    have sc := ReorderedSlots.cache 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide) keepB_geometry.2.1
    rw [loopPCB, restB, rawFB, newIB, StairSqLoopB.loopNC, StairSqLoopB.restNC,
      B95Research.I, B95Research.rawI, B95Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [Challenge.gateSlots_append]
    omega
  have nc := StairSqLoopB.loopNC_slots
  rw [loopB, hr]
  omega

theorem loopB_frame (base : BasisState) (clean : K0.PairClean base) (hsum : base K0.core.sumCarry = false)
    (O E O' : Nat) (hE : E < 2 ^ 129)
    (mid : Triple (BState K0 base O E (4294968272 * regValue (hiReg K0) base)) (FullBTemp.middle K0 G0)
      (BState K0 base O' E (4294968272 * regValue (hiReg K0) base))) :
    Triple (BState K0 base O E 0) loopB (BState K0 base O' E 0) := by
  have pcFrame : Triple (BState K0 base O E 0) loopPCB (BState K0 base O' E 0) := by
    intro s m hsB
    obtain ⟨hzFull, hb, hi, _, _⟩ := zero_regs K0 LowAccCarryDevelop.layout_nodup base clean O E 0 s.basis hsB
    have hz : ∀ q ∈ ReorderedBPrefixResearch.pad, s.basis q = false := fun q hq => hzFull q ((FullPadDevelop.pad_sublist K0).subset hq)
    have ha : regValue LowAccCarryDevelop.ga s.basis = 0 := LowAccCarryDevelop.ga_bstate_value base s.basis clean O E 0 hsB (by decide)
    have small : regValue ReorderedBPrefixResearch.acc s.basis = 0 := by
      rw [regValue_take_mod LowAccCarryDevelop.ga 161 (by rw [LowAccCarryDevelop.ga_length]; decide), ha]; rfl
    have headEq : run loopPCB m s = run coreB m s := by
      have cl : ∀ q ∈ KnownBHeadResearch.clean, s.basis q = false := by
        intro q hq; simp only [KnownBHeadResearch.clean, List.mem_append, List.mem_singleton] at hq
        rcases hq with ((hq | hq) | hq) | rfl
        · exact (regValue_zero _ _).mp small q hq
        · exact hz q hq
        · exact hb q hq
        · exact hi
      have hheadEq : B95Research.head = KnownBHeadResearch.original := by
        unfold B95Research.head KnownBHeadResearch.original; rfl
      have shape : coreB = KnownBHeadResearch.original ++ restB := by
        rw [coreB, newFB, restB, hheadEq]
        have g (A B C D E F G H : Program) : (((A ++ B ++ C ++ D) ++ E ++ F) ++ (G ++ H)) = A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H) := by simp only [List.append_assoc]
        exact g _ _ _ _ _ _ _ _
      exact (ClearContextResearch.append_at KnownBHeadResearch.output KnownBHeadResearch.original restB s m
        KnownBHeadResearch.measurements (KnownBHeadResearch.run_eq s m cl)).trans (congrArg (fun P => run P m s) shape.symm)
    rw [headEq]
    have zero : ∀ q ∈ ReorderedBSupportResearch.hosts, s.basis q = false := by
      intro q hq; rcases List.mem_cons.mp hq with rfl | hq
      · have away := ParkCarryDevelop.sumCarry_off_regs K0 LowAccCarryDevelop.layout_nodup
        exact (hsB.2.2.2 _ away.1 away.2.1 away.2.2).trans hsum
      · exact LowAccCarryDevelop.initial_hosts_zero base s.basis clean O E hsB q hq
    have good := fun r => ReorderedBReadyResearch.original_ready base clean O E O' mid s r hsB
    have hc : ExtraCarryDomain.Clean s.basis := ⟨bstate_clean K0 LowAccCarryDevelop.layout_nodup base clean O E s.basis hsB, by change regValue (eReg K0) s.basis < 2 ^ 129; rw [hsB.2.1]; exact hE⟩
    have ready : WReady ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank
        ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src (regValue ReorderedBPrefixResearch.src s.basis)
        (middleState B95Research.oldF B95Research.oldM s m) :=
      BRelocatedReadyResearch.patched_after s m hc hz hb hi ha zero good
    have f := ReorderedAPlain.build_triple ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src
      ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits s.basis hz hb hi s
      (m.take (measurementCount B95Research.oldF)) ⟨small, fun _ _ => rfl⟩
    have flag0 := (f.2.2 4762 (by simp only [ReorderedBPrefixResearch.acc, ReorderedBPrefixResearch.pad, ReorderedBPrefixResearch.bank, ReorderedBPrefixResearch.cin, ReorderedBPrefixResearch.src, ReorderedBPrefixResearch.ga, LowAccCarryDevelop.ga, LowAccCarryDevelop.L, FullBReady.L, show Baselines.layout.dialogStreamedSquareWide = K0 from rfl, K0_eq]; decide +kernel)).trans hc.1.modFlag
    have e : B95Research.oldF = ReorderedAPlain.build ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
        ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src := rfl
    have flag : (run B95Research.oldF (m.take (measurementCount B95Research.oldF)) s).basis 4762 = false :=
      (congrArg (fun P => (run P (m.take (measurementCount B95Research.oldF)) s).basis 4762 = false) e).mpr flag0
    have one := core_plainB s m hz hb hi small zero ready flag
    have two : run BPatchedLoopResearch.core m s =
        run (B95Research.oldF ++ B95Research.oldM ++ ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) m s := by
      simpa only [BPatchedLoopResearch.core, B95Research.oldF, B95Research.oldM] using
        HighCachedLoopBResearch.loop_eq ReorderedBPrefixResearch.acc ReorderedBMiddlePatchesResearch.output
          ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.fits rfl s m hz hb hi small
          ReorderedBSupportResearch.fresh (fun q hq => (ReorderedBSupportResearch.plain_free q hq).1)
          (fun q hq => (ReorderedBSupportResearch.plain_free q hq).2) ReorderedBMiddlePatchesResearch.fresh zero ready
    rw [one.trans two.symm]
    exact BPatchedLoopResearch.core_frame base clean hsum O E O' hE mid s m hsB
  intro s m hsB
  have r := pcFrame s m hsB
  have zIn := (zero_regs K0 LowAccCarryDevelop.layout_nodup base clean O E 0 s.basis hsB).2.2.2.1
  have zOut := (zero_regs K0 LowAccCarryDevelop.layout_nodup base clean O' E 0 (run loopPCB m s).basis r.2).2.2.2.1
  have hOut : ∀ q ∈ hs, (run loopPCB m s).basis q = false := fun q hq => zOut q (StairSqLoopB.holes_geometry44.2.1 q hq)
  have hEq : run loopB m s = run loopPCB m s := by
    apply hostRename_run_eq (StairSqLoopB.pairs hs) loopPCB s m
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact zIn y (StairSqLoopB.holes_geometry44.2.1 y hy)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact LowAccCarryDevelop.initial_hosts_zero base s.basis clean O E hsB _ (StairSqLoopB.holes_geometry44.2.2 y hy)
    · intro ab hab; obtain ⟨y, hy, he⟩ := List.mem_map.mp hab
      have h1 : ab.1 = y := by rw [← he]
      rw [h1]; exact hOut y hy
    · exact loopB_pairs_free
  rw [hEq]; exact r

private def efCheckB : List Wire :=
  [4726, 4727, 4728, 4729, 4730, 4731, 4732, 4733, 4734, 4735, 4736, 4737, 4738, 4739, 4740, 4741,
   4742, 4743, 4744, 4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752, 4753, 4754, 4755, 4756]

private theorem efold_avoids_check : ∀ q ∈ efCheckB, q ∉ wires StairSquareBEFoldK.efold := by
  have hflip : ∀ q ∈ efCheckB, q ∉ wires (ControlLoan1589BFFold.eFlip K0 G0) :=
    StairSquareBChecks.touchedAny_spec _ _
      (StairSquareBChecks.K2Hit.touchedAny_of_mask _ _ (by rw [K0_eq, G0_eq]; decide +kernel))
  have hfill : ∀ q ∈ efCheckB, q ∉ StairSquareBChecks.K2Fill.efillS K0 :=
    StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [K0_eq]; decide +kernel)
  have hsup := StairSquareBChecks.K2Fill.efill_support K0 hwK LowAccCarryDevelop.layout_nodup
  have h3 : ∀ q ∈ efCheckB,
      q ∉ (StairSquareBEFold.coreB K0).out ++ (StairSquareBEFold.coreB K0).carry ++
        [(StairSquareBEFold.coreB K0).high, (StairSquareBEFold.coreB K0).cin,
         (StairSquareBEFold.coreB K0).flag] ++ ECDSAAdd.Entrant.accReg K0 :=
    StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [K0_eq]; decide +kernel)
  intro q hq bad
  simp only [StairSquareBEFoldK.efold, StairSquareBEFold.eFoldB, StairSquareBEFold.accFoldB,
    lb_eq_K0, cb_eq_G0, wires_append, Finset.mem_union] at bad
  rcases bad with hw | ((hw | hw) | hw) | hw
  · exact hflip q hq hw
  · exact hfill q hq (List.mem_toFinset.mp (hsup.1 hw))
  · have hs := StairSquareBMapped.qprogM_support (StairSquareBEFold.coreB K0)
      (StairSquareBEFold.bitsB K0) SquareReduction.p hw
    rw [StairSquareBEFold.bitsB_wires] at hs
    exact h3 q hq (List.mem_toFinset.mp hs)
  · exact hfill q hq (List.mem_toFinset.mp (hsup.2 hw))
  · exact hflip q hq hw

/-- `efoldB` satisfies `StairSqBodyB.EFoldOK` AND avoids `workTB`, `hs`, and `normFlag`. -/
theorem efoldB_hostFree : ∀ ab ∈ efSwapB, ab.2 ∉ wires StairSquareBEFoldK.efold := fun ab hab =>
  efold_avoids_check ab.2 ((by rw [efSwapB_lit]; decide +kernel : ∀ p ∈ efSwapB, p.2 ∈ efCheckB) ab hab)

theorem efoldB_ok : StairSqBodyB.EFoldOK efoldB := by
  have baseOK := StairSqBodyB.efold_ok
  refine ⟨?_, ?_, ?_, hostRename_physical _ _ baseOK.2.2.2⟩
  · intro b clean O E hO s m hsB
    have r := baseOK.1 b clean O E hO s m hsB
    have hEq : run efoldB m s = run StairSquareBEFoldK.efold m s := by
      apply hostRename_run_eq efSwapB StairSquareBEFoldK.efold s m
      · intro ab hab
        have h1 : ab.1 ∈ LowAccCarryDevelop.hosts88 := (by rw [efSwapB_lit, hosts88_fast]; decide +kernel : ∀ x ∈ holesOf efSwapB, x ∈ LowAccCarryDevelop.hosts88) ab.1 (List.mem_map.mpr ⟨ab, hab, rfl⟩)
        exact LowAccCarryDevelop.initial_hosts_zero b s.basis clean O E hsB ab.1 h1
      · intro ab hab
        have h2 : ab.2 ∈ LowAccCarryDevelop.hosts88 := List.mem_of_mem_take (work_T_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ab hab).2.2.1
        exact LowAccCarryDevelop.initial_hosts_zero b s.basis clean O E hsB ab.2 h2
      · intro ab hab
        have h1 : ab.1 ∈ LowAccCarryDevelop.hosts88 := (by rw [efSwapB_lit, hosts88_fast]; decide +kernel : ∀ x ∈ holesOf efSwapB, x ∈ LowAccCarryDevelop.hosts88) ab.1 (List.mem_map.mpr ⟨ab, hab, rfl⟩)
        exact LowAccCarryDevelop.initial_hosts_zero b (run StairSquareBEFoldK.efold m s).basis clean _ E r.2 ab.1 h1
      · exact efoldB_hostFree
    rw [hEq]; exact r
  · intro q hq
    have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree hq
    rcases Finset.mem_union.mp sub with h | h
    · exact baseOK.2.1 (Finset.mem_sdiff.mp h).1
    · have subK : ∀ x ∈ hostsOf efSwapB, x ∈ K0.wires := by rw [efSwapB_lit, K0_eq]; decide +kernel
      rw [lb_eq_K0, cb_eq_G0]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem G0 (subK q (List.mem_toFinset.mp h)))
  · intro q hq bad
    have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
    rcases Finset.mem_union.mp sub with h | h
    · exact baseOK.2.2.1 q hq (Finset.mem_sdiff.mp h).1
    · exact (by rw [efSwapB_lit, holesA_lit]; decide +kernel : ∀ x ∈ StairSqLoopA.holes, x ∉ hostsOf efSwapB) q hq (List.mem_toFinset.mp h)

theorem efoldB_avoids_workTB : ∀ q ∈ workTB, q ∉ wires efoldB := by
  intro q hq bad
  by_cases hD : q = D0
  · subst hD
    have hsup := efoldB_ok.2.1 bad
    rw [lb_eq_K0, cb_eq_G0] at hsup
    exact (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (List.mem_toFinset.mp hsup)
  · by_cases hh : q ∈ holesOf efSwapB
    · exact hostRename_avoids efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree q hh bad
    · have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
      rcases Finset.mem_union.mp sub with h | h
      · exact efold_avoids_check q ((by rw [workTB_lit, D0_eq, efSwapB_lit]; decide +kernel : ∀ x ∈ workTB, x ≠ D0 → x ∉ holesOf efSwapB → x ∈ efCheckB) q hq hD hh) (Finset.mem_sdiff.mp h).1
      · exact (by rw [workTB_lit, efSwapB_lit]; decide +kernel : ∀ x ∈ workTB, x ∉ hostsOf efSwapB) q hq (List.mem_toFinset.mp h)

theorem efoldB_avoids_hs : ∀ q ∈ hs, q ∉ wires efoldB := by
  intro q hq bad
  have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
  rcases Finset.mem_union.mp sub with h | h
  · exact StairSquareBEFoldK.efold_avoids q hq (Finset.mem_sdiff.mp h).1
  · exact (by rw [efSwapB_lit, hs_lit]; decide +kernel : ∀ x ∈ hs, x ∉ hostsOf efSwapB) q hq (List.mem_toFinset.mp h)

theorem efoldB_normFlag : K0.core.normFlag ∉ wires efoldB := by
  intro bad
  have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
  rcases Finset.mem_union.mp sub with h | h
  · exact StairSquareBEFoldK.efold_normFlag (Finset.mem_sdiff.mp h).1
  · exact (by rw [efSwapB_lit, K0_eq]; decide +kernel : K0.core.normFlag ∉ hostsOf efSwapB) (List.mem_toFinset.mp h)

theorem bodyB_ok : BodyBOK bodyB := by
  have hn := LowAccCarryDevelop.layout_nodup
  have hcw : G0 ∉ K0.wires := (List.nodup_cons.mp controlND).1
  have sup : wires bodyB ⊆ (G0 :: K0.wires).toFinset := by
    have sp1 := directFold_rename_support foldPairsB (negP K0) (negP_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
    have sp2 := directFold_rename_support foldPairsB (rot128F K0) (rot128F_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
    have direct_in_K0 (f : MeasuredSquareFold) (hc : ∀ q, f.src.count q ≤ K0.core.product.count q) :
        wires (directFoldQTq K0 f) ⊆ K0.wires.toFinset := by
      intro q hq
      have h1 := List.count_pos_iff.mpr (List.mem_toFinset.mp (directFoldQ_supportTq K0 f hq))
      have h2 := hc q
      simp only [directWires, List.count_append, List.count_cons, List.count_nil] at h1
      exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by
        simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires,
          List.count_append, List.count_cons, List.count_nil]; omega))
    have f1 : wires dF1B ⊆ (G0 :: K0.wires).toFinset := by
      intro q hq; rcases Finset.mem_union.mp (sp1 hq) with h | h
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (direct_in_K0 (negP K0) (negP_count K0) (Finset.mem_sdiff.mp h).1)))
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).2.2.1)
    have f2 : wires dF2B ⊆ (G0 :: K0.wires).toFinset := by
      intro q hq; rcases Finset.mem_union.mp (sp2 hq) with h | h
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (direct_in_K0 (rot128F K0) (rot128F_count K0) (Finset.mem_sdiff.mp h).1)))
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).2.2.1)
    have park := ParkCarry10Develop.body_support StairSqBodyB.LB LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup StairSqBodyB.cB
    have fl : wires loopB ⊆ (G0 :: K0.wires).toFinset := by
      rw [← lb_eq_K0, ← cb_eq_G0]
      exact loopB_support.trans (fun q hq => park (FullB99OptTemp.actual_subset hq))
    have fpad : wires (ReorderedRecordPadding.program 4 K0.core.cin) ⊆ (G0 :: K0.wires).toFinset := by
      intro q hq; rw [Finset.mem_singleton.mp (padding_wires 4 K0.core.cin hq)]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (by simp [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires]))
    have r0 := StairSqBodyB.bodyB_support44 hs (List.Sublist.refl _)
    simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
      lb_eq_K0, cb_eq_G0, wires_append, Finset.union_subset_iff] at r0
    simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
      wires_append, Finset.union_subset_iff]
    have heSup : wires efoldB ⊆ (G0 :: K0.wires).toFinset := by rw [← lb_eq_K0, ← cb_eq_G0]; exact efoldB_ok.2.1
    exact ⟨⟨f1, f2, ⟨r0.1.2.2.1.1, fl, r0.1.2.2.1.2.2.1, r0.1.2.2.1.2.2.2⟩, heSup, r0.1.2.2.2.2⟩, fpad⟩
  refine ⟨sup, ?_⟩
  intro base M hM hP hc hsum O hO hg hSource
  have hb : M ^ 2 < 2 ^ 256 := by simpa using square_bound M 128 hM
  have views := accA_views K0 hwK base M hM hP
  have v1 : K0.MeasuredFoldView base (negP K0) := views (.inl (negP K0)) (by simp [accAMix])
  have v2 : K0.MeasuredFoldView base (rot128F K0) := views (.inl (rot128F K0)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP K0) = M ^ 2 := by
    simp only [measuredFoldPayload, negP, pow_zero, Nat.mul_one]
    rw [K0.product_take_value hwK base (M ^ 2) hP 256 (by omega), Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F K0) = (M ^ 2 / 2 ^ 128) % 2 ^ 128 + 2 ^ 128 * (M ^ 2 % 2 ^ 128) := by
    simp only [measuredFoldPayload, rot128F, pow_zero, Nat.mul_one]
    exact K0.rotated128_value hwK base (M ^ 2) hP
  have f1 : ∀ O0, O0 < SquareReduction.p → Triple (SquareFrame K0.core.out base O0) dF1B
      (SquareFrame K0.core.out base ((M ^ 2 + (SquareReduction.p - 1 - O0)) % SquareReduction.p)) := by
    intro O0 hO0 s m hf
    have eq1 := directFold_rename_run foldPairsB (negP K0) (negP_count K0) (negP_length K0 hwK) rfl rfl
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).1, (foldPairsB_geom.2.2.2.1 ab hab).2.1⟩)
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).2.2.1, (foldPairsB_geom.2.2.2.1 ab hab).2.2.2.1⟩)
      base v1 hc O0 hO0 s m hf
    rw [dF1B, eq1]
    have h := directFoldQ_frameTq K0 hwK hn base (negP K0) v1 rfl hc (negP_length K0 hwK) rfl O0 hO0 s m hf
    rwa [pay1] at h
  have f2 : ∀ O0, O0 < SquareReduction.p → Triple (SquareFrame K0.core.out base O0) dF2B
      (SquareFrame K0.core.out base
        (((M ^ 2 / 2 ^ 128) % 2 ^ 128 + 2 ^ 128 * (M ^ 2 % 2 ^ 128) + (SquareReduction.p - 1 - O0)) % SquareReduction.p)) := by
    intro O0 hO0 s m hf
    have eq2 := directFold_rename_run foldPairsB (rot128F K0) (rot128F_count K0) (rot128F_length K0 hwK) rfl rfl
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).1, (foldPairsB_geom.2.2.2.1 ab hab).2.1⟩)
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).2.2.1, (foldPairsB_geom.2.2.2.1 ab hab).2.2.2.1⟩)
      base v2 hc O0 hO0 s m hf
    rw [dF2B, eq2]
    have h := directFoldQ_frameTq K0 hwK hn base (rot128F K0) v2 rfl hc (rot128F_length K0 hwK) rfl O0 hO0 s m hf
    rwa [pay2] at h
  have raw := StairSquareBBody.frameG StairSqBodyB.LB LowAccCarryDevelop.layout_widths hn StairSqBodyB.cB LowAccCarryDevelop.control_outside
    loopB (by rw [lb_eq_K0]; exact loopB_frame)
    efoldB (fun b clean O0 E0 hO0 => efoldB_ok.1 b clean O0 E0 hO0)
    LocalRebuild.improved
    (fun b outB clean O0 E0 B0 hb old => LocalRebuildLift.transfer b outB clean O0 E0 B0 hb old)
    base M hM (by rw [lb_eq_K0]; exact hP) (by rw [lb_eq_K0]; exact hc) (by rw [lb_eq_K0]; exact hsum) O hO
    (by rw [cb_eq_G0]; exact hg) (by rw [lb_eq_K0, cb_eq_G0]; exact hSource)
    dF1B dF2B (by rw [lb_eq_K0]; exact f1) (by rw [lb_eq_K0]; exact f2)
  rw [lb_eq_K0, cb_eq_G0] at raw
  show Triple _ (StairSquareBBody.bodyG K0 dF1B dF2B loopB efoldB LocalRebuild.improved ++
    ReorderedRecordPadding.program 4 K0.core.cin) _
  apply raw.seq
  intro t r ht
  have hz : t.basis K0.core.cin = false :=
    (ht.2 K0.core.cin (K0.pairAuxAway hn _ (by simp)).2).trans hc.cin
  rw [ReorderedRecordPadding.run_zero 4 K0.core.cin t r hz]
  exact ⟨rfl, ht⟩

private theorem rebuild_chunk0_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk0 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk0 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk1_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk1 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk1 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk2_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk2 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk2 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk3_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk3 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk3 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk4_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk4 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk4 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk5_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk5 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk5 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk6_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk6 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk6 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk7_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk7 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk7 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk8_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk8 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk8 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk9_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk9 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk9 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk10_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk10 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk10 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk11_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk11 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk11 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk12_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk12 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk12 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk13_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk13 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk13 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk14_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk14 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk14 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk15_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk15 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk15 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk16_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk16 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk16 workTB (by rw [workTB_lit]; decide +kernel)

private theorem rebuild_chunk17_workTB_free :
    StairSquareBChecks.touchedAny LocalRebuild.chunk17 workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk17 workTB (by rw [workTB_lit]; decide +kernel)

private theorem bodyB_eAdd_workTB_free :
    StairSquareBChecks.touchedAny (ControlLoan1589BFFold.eAddLo K0) workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask _ _ (by rw [workTB_lit, K0_eq]; decide +kernel)

private theorem bodyB_park_workTB_free :
    StairSquareBChecks.touchedAny (ParkCarryDevelop.program (ControlLoan1589BFFold.eU K0) K0.core.sumCarry) workTB = false :=
  StairSquareBChecks.K2Hit.touchedAny_of_mask _ _ (by rw [workTB_lit, K0_eq]; decide +kernel)

theorem bodyB_avoids_workTB : ∀ q ∈ workTB, q ∉ wires bodyB := by
  intro q hq bad
  by_cases hD : q = D0
  · subst hD
    exact (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (List.mem_toFinset.mp (bodyB_ok.support bad))
  have hq31 : q ∈ workTB.take 31 := (by rw [workTB_lit, D0_eq]; decide +kernel : ∀ x ∈ workTB, x ≠ D0 → x ∈ workTB.take 31) q hq hD
  have hn := LowAccCarryDevelop.layout_nodup
  have a1 := hostRename_avoids foldPairsB (directFoldQTq K0 (negP K0)) foldPairsB_geom.1
    (fun ab hab => directFoldQ_free K0 hn (negP K0) (negP_count K0) ab.2 (by simp [directFree, (foldPairsB_geom.2.2.2.1 ab hab).2.2.1]))
  have a2 := hostRename_avoids foldPairsB (directFoldQTq K0 (rot128F K0)) foldPairsB_geom.1
    (fun ab hab => directFoldQ_free K0 hn (rot128F K0) (rot128F_count K0) ab.2 (by simp [directFree, (foldPairsB_geom.2.2.2.1 ab hab).2.2.1]))
  rw [foldPairsB_geom.2.1] at a1 a2
  have offEAdd : ∀ x ∈ workTB, x ∉ wires (ControlLoan1589BFFold.eAddLo K0) :=
    StairSquareBChecks.touchedAny_spec _ _
      (bodyB_eAdd_workTB_free)
  have offPark : ∀ x ∈ workTB, x ∉ wires (ParkCarryDevelop.program (ControlLoan1589BFFold.eU K0) K0.core.sumCarry) :=
    StairSquareBChecks.touchedAny_spec _ _
      (bodyB_park_workTB_free)
  have offESub : ∀ x ∈ workTB, x ∉ wires (ControlLoan1589BFFold.eSubK K0) := fun x hx hw =>
    StairSquareBChecks.LT48B.disj_of_maskL _ _
      (by rw [workTB_lit, show StairSquareBChecks.LB = K0 from rfl, K0_eq]; decide +kernel) x hx
      (List.mem_toFinset.mp (StairSquareBChecks.eSubK_support (by rw [show StairSquareBChecks.LB = K0 from rfl]; exact hw)))
  have offReb : ∀ x ∈ workTB, x ∉ wires LocalRebuild.improved := by
    intro x hx hw
    have hact : x ∈ wires LocalRebuild.actual := LocalRebuildResources.support hw
    rw [LocalRebuild.literal, LocalRebuild.program] at hact
    simp only [wires_append, Finset.mem_union] at hact
    rcases hact with (((h | h) | (h | h)) | ((h | h) | (h | (h | h)))) | (((h | h) | (h | h)) | ((h | h) | (h | (h | h))))
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk0_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk1_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk2_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk3_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk4_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk5_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk6_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk7_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk8_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk9_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk10_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk11_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk12_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk13_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk14_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk15_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk16_workTB_free) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (rebuild_chunk17_workTB_free) x hx h
  simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, wires_append, Finset.mem_union] at bad
  rcases bad with ((b | b | (b | b | b | b) | b | b) | b)
  · exact a1 q hq31 b
  · exact a2 q hq31 b
  · exact offEAdd q hq b
  · exact loopB_avoids_workTB q hq b
  · exact offPark q hq b
  · exact offESub q hq b
  · exact efoldB_avoids_workTB q hq b
  · exact offReb q hq b
  · exact (by rw [workTB_lit, K0_eq]; decide +kernel : ∀ x ∈ workTB, x ≠ K0.core.cin) q hq (Finset.mem_singleton.mp (padding_wires 4 K0.core.cin b))

theorem bodyB_avoids_hs : ∀ q ∈ hs, q ∉ wires bodyB := by
  intro q hq bad
  have sp1 := directFold_rename_support foldPairsB (negP K0) (negP_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have sp2 := directFold_rename_support foldPairsB (rot128F K0) (rot128F_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have h44 := StairSqBodyB.bodyB_avoids44 hs (List.Sublist.refl _) q hq
  simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
    StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, wires_append, Finset.mem_union, not_or] at h44
  simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, wires_append, Finset.mem_union] at bad
  rcases bad with ((b | b | (b | b | b | b) | b | b) | b)
  · rcases Finset.mem_union.mp (sp1 b) with h | h
    · exact h44.1.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).1 hq
  · rcases Finset.mem_union.mp (sp2 b) with h | h
    · exact h44.1.2.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).1 hq
  · exact h44.1.2.2.1.1 b
  · exact loopB_avoids_hs q hq b
  · exact h44.1.2.2.1.2.2.1 b
  · exact h44.1.2.2.1.2.2.2 b
  · exact efoldB_avoids_hs q hq b
  · exact h44.1.2.2.2.2 b
  · exact h44.2 b

theorem bodyB_normFlag : K0.core.normFlag ∉ wires bodyB := by
  have sp1 := directFold_rename_support foldPairsB (negP K0) (negP_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have sp2 := directFold_rename_support foldPairsB (rot128F K0) (rot128F_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have hnf := StairSqBodyB.bodyB_normFlag44 hs (List.Sublist.refl _)
    (StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.middle_norm _ (List.mem_singleton_self _))
  simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
    StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, wires_append, Finset.mem_union, not_or] at hnf
  intro bad
  simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, wires_append, Finset.mem_union] at bad
  rcases bad with ((b | b | (b | b | b | b) | b | b) | b)
  · rcases Finset.mem_union.mp (sp1 b) with h | h
    · exact hnf.1.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 _ (List.mem_toFinset.mp h)).2.1 rfl
  · rcases Finset.mem_union.mp (sp2 b) with h | h
    · exact hnf.1.2.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 _ (List.mem_toFinset.mp h)).2.1 rfl
  · exact hnf.1.2.2.1.1 b
  · exact loopB_normFlag b
  · exact hnf.1.2.2.1.2.2.1 b
  · exact hnf.1.2.2.1.2.2.2 b
  · exact efoldB_normFlag b
  · exact hnf.1.2.2.2.2 b
  · exact hnf.2 b

theorem bodyB_physical : GatePhysical bodyB := by
  have p0 := StairSqBodyB.bodyB_physical hs
  simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
    StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, gatePhysical_append] at p0
  simp only [bodyB, dF1B, dF2B, efoldB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, gatePhysical_append]
  exact ⟨⟨hostRename_physical _ _ p0.1.1, hostRename_physical _ _ p0.1.2.1,
    ⟨p0.1.2.2.1.1, hostRename_physical _ _ loopPCB_physical, p0.1.2.2.1.2.2.1, p0.1.2.2.1.2.2.2⟩,
    hostRename_physical _ _ StairSquareBEFoldK.efold_physical, p0.1.2.2.2.2⟩, p0.2⟩

theorem bodyB_counts :
    toffoliCount bodyB = toffoliCount B95PaddedResearch.body + 89 ∧
    measurementCount bodyB = measurementCount B95PaddedResearch.body := by
  have c0 := StairSqBodyB.bodyB_counts hs
  have cl_old := StairSqLoopB.loopB_counts hs
  have cl_new := loopB_counts
  have r1 := hostRename_counts foldPairsB (directFoldQTq K0 (negP K0))
  have r2 := hostRename_counts foldPairsB (directFoldQTq K0 (rot128F K0))
  have re := hostRename_counts efSwapB StairSquareBEFoldK.efold
  simp only [bodyB, dF1B, dF2B, efoldB, StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG,
    LowAccCarryDevelop.foldFor, StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, toffoliCount_append, measurementCount_append,
    r1.1, r1.2, r2.1, r2.2, re.1, re.2] at c0 ⊢
  exact ⟨by linarith only [c0.1, cl_old.1, cl_new.1], by linarith only [c0.2, cl_old.2, cl_new.2]⟩

theorem bodyB_slots : Challenge.gateSlots bodyB + 793 ≤ Challenge.gateSlots B95PaddedResearch.body := by
  have s0 := StairSqBodyB.bodyB_slots hs
  have sl_old := StairSqLoopB.loopB_slots hs
  have sl_new := loopB_slots
  have r1 := hostRename_slots foldPairsB (directFoldQTq K0 (negP K0))
  have r2 := hostRename_slots foldPairsB (directFoldQTq K0 (rot128F K0))
  have re := hostRename_slots efSwapB StairSquareBEFoldK.efold
  simp only [bodyB, dF1B, dF2B, efoldB, StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG,
    LowAccCarryDevelop.foldFor, StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, Challenge.gateSlots_append, r1, r2, re] at s0 ⊢
  linarith only [s0, sl_old, sl_new]

end BodyB

/-! ## Branch C body (`keepC` = 27 carries, avoids `workTC` and `hs`) -/

section BodyC
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq

private theorem lc_eq_K0 : C163Low4Middle.L = K0 := rfl

def keepC : List Wire := C105Research.keepK.filter (fun q => !workTC.contains q)

theorem keepC_geometry : keepC.Nodup ∧ keepC.length = 27 ∧
    (∀ q ∈ keepC, q ∈ C105Research.hosts) ∧
    (∀ q ∈ workTC, q ∉ keepC) ∧
    (∀ i, i < 44 → C163Low4Middle.hs.getD i 0 ∉ keepC) ∧
    (∀ q ∈ keepC, q ∈ allowedWires) := by
  have hall : ∀ q ∈ keepC, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [keepC, keepKC_fast, workTC_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [keepC, keepKC_fast, workTC_lit, hs_lit]; decide +kernel))
  have hr : keepC.Nodup ∧ keepC.length = 27 ∧
      (∀ q ∈ keepC, q ∈ C105Research.hosts) ∧
      (∀ q ∈ workTC, q ∉ keepC) ∧
      (∀ i, i < 44 → C163Low4Middle.hs.getD i 0 ∉ keepC) := by
    rw [keepC, keepKC_fast, hostsC105_fast, hsC_fast, workTC_lit]; decide +kernel
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, hall⟩

def rawFC : Program := ReorderedGenericCache.cachedAdd 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
def newFC : Program := C105Research.head ++ C105LowEraseResearch.clear ++ rawFC ++ C105Research.top
def newIC : Program := C105Research.preInv ++ ReorderedConsumedSub.consumed 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
def coreC : Program := (newFC ++ C105Research.M ++ newIC) ++ (C105LowEraseResearch.clear ++ C105Research.tail)
def restC : Program := C105LowEraseResearch.clear ++ rawFC ++ C105Research.top ++ C105Research.M ++ newIC ++ C105LowEraseResearch.clear ++ C105Research.tail
def loopPCC : Program := SignCHead.head ++ restC
def loopC : Program := hostRename (StairSqLoopC.pairs hs) loopPCC
def foldPairsC : List (Wire × Wire) := workTC.zip (K0.core.pad.take 34)
def dFC : Program := hostRename foldPairsC (directFoldQTq K0 (negRot K0))
def bodyC : Program := (dFC ++ loopC) ++ ReorderedRecordPadding.program 7 K0.core.cin
def bodyCPlain : Program := C105SignResearch.directBody loopC

theorem foldPairsC_geom :
    (holesOf foldPairsC ++ hostsOf foldPairsC).Nodup ∧
    holesOf foldPairsC = workTC ∧
    hostsOf foldPairsC = K0.core.pad.take 34 ∧
    (∀ ab ∈ foldPairsC, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out ∧ ab.2 ∈ allowedWires) ∧
    (∀ q ∈ hostsOf foldPairsC, q ∉ hs ∧ q ∈ K0.wires ∧ q ∈ allowedWires) := by
  have hall : ∀ q ∈ hostsOf foldPairsC, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsC, workTC_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [foldPairsC, workTC_lit, K0_eq, hs_lit]; decide +kernel))
  have hK : ∀ q ∈ hostsOf foldPairsC, q ∈ K0.wires :=
    StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsC, workTC_lit, K0_eq]; decide +kernel)
  have hr : (holesOf foldPairsC ++ hostsOf foldPairsC).Nodup ∧
      holesOf foldPairsC = workTC ∧
      hostsOf foldPairsC = K0.core.pad.take 34 ∧
      (∀ ab ∈ foldPairsC, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out) ∧
      (∀ q ∈ hostsOf foldPairsC, q ∉ hs) := by rw [foldPairsC, workTC_lit, K0_eq, hs_lit]; decide +kernel
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_, ?_⟩
  · intro ab hab; have h := hr.2.2.2.1 ab hab
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hall ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩)⟩
  · intro q hq; exact ⟨hr.2.2.2.2 q hq, hK q hq, hall q hq⟩

private theorem keepC_sub (q : Wire) (hq : q ∈ keepC) : q ∈ C105Research.hosts := keepC_geometry.2.2.1 q hq

private theorem core_plainC (s : State) (m : List Bool)
    (hz : ∀ q ∈ C105PrefixResearch.pad, s.basis q = false) (hb : ∀ q ∈ C105PrefixResearch.bank, s.basis q = false)
    (hi : s.basis C105PrefixResearch.cin = false) (ha : regValue C105PrefixResearch.acc s.basis = 0)
    (zero : ∀ q ∈ ReorderedCFixed.hosts, s.basis q = false)
    (after : WReady C105PrefixResearch.acc C105PrefixResearch.pad C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src
      (regValue C105PrefixResearch.src s.basis) (middleState C105Research.oldF C105Research.oldM s m))
    (flag : (run C105Research.oldF (m.take (measurementCount C105Research.oldF)) s).basis 4762 = false) :
    run coreC m s = run (C105Research.oldF ++ C105Research.oldM ++
      ReorderedCPlain.unbuild C105PrefixResearch.acc C105PrefixResearch.pad C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src) m s := by
  let H := regValue C105PrefixResearch.src s.basis
  let vs := ReorderedCacheBits.values 4 27 H (976 * H / 1024)
  have keepSubK (q : Wire) (hq : q ∈ keepC) : q ∈ C105Research.keepK := (List.mem_filter.mp hq).1
  have fwdM : measurementCount newFC = measurementCount C105Research.F := by
    have h := (ReorderedGenericCache.count_balance 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide)).2.1
    simp only [newFC, rawFC, C105Research.F, C105Research.rawF, measurementCount_append]; rw [h]
  have invM : measurementCount newIC = measurementCount C105Research.I := by
    have h := ReorderedConsumedSub.measurement_eq 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide)
    simp only [newIC, C105Research.I, C105Research.rawI, measurementCount_append]; rw [h]
  have fwdVal : (((C105Research.cs.drop 4).take 27).map (run (carryPrefix (4 + 27) C105Research.xs C105Research.ys C105Research.cs C105PrefixResearch.cin) []
      (run (C105Research.head ++ C105LowEraseResearch.clear)
        ((m.take (measurementCount C105Research.F)).take (measurementCount (C105Research.head ++ C105LowEraseResearch.clear))) s)).basis) = vs := by
    let m0 := (m.take (measurementCount C105Research.F)).take (measurementCount (C105Research.head ++ C105LowEraseResearch.clear))
    let u := run C105Research.head m0 s
    let t := run (C105Research.head ++ C105LowEraseResearch.clear) m0 s
    have te : t = C105LowEraseResearch.erase u := C105Research.prefix_erased s m0 hz hb hi ha
    have hH : H < 2 ^ 130 := by simpa only [H, C105PrefixResearch.source_length] using regValue_lt C105PrefixResearch.src s.basis
    have ready := CHeadArithmeticResearch.ready C105PrefixResearch.acc C105PrefixResearch.pad C105PrefixResearch.bank
      C105PrefixResearch.cin C105PrefixResearch.src C105PrefixResearch.acc_length C105PrefixResearch.source_length C105PrefixResearch.fits s m0 hz hb hi ha
    have eb (q : Wire) (hq : q ∈ C105Research.domain) : t.basis q = u.basis q := by
      rw [te]; exact C105LowEraseResearch.bit_same _ q (C105Research.domain_away_low q hq)
    have er (r : List Wire) (sub : ∀ q ∈ r, q ∈ C105Research.domain) : regValue r t.basis = regValue r u.basis :=
      regValue_congr _ _ _ (fun q hq => eb q (sub q hq))
    exact ReorderedCacheBits.forward_values 4 27 H (((2 ^ 140 - 48 * H) % 2 ^ 140) / 1024) (976 * H / 1024)
      C105Research.xs C105Research.ys C105Research.cs C105PrefixResearch.cin t
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide) C105Research.raw_nd
      (fun q hq => (eb q (C105Research.c_in q hq)).trans (ready.1 q hq))
      ((eb _ C105Research.cin_in).trans ready.2.1)
      ((er _ C105Research.x_in).trans ready.2.2.1)
      ((er _ C105Research.y_in).trans ready.2.2.2)
      (fun j hj => by simpa only [show 130 + 10 = 140 by decide] using ReorderedCacheArithmetic.high_add_low 130 (4 + j + 1) H (by omega) hH)
  have forward : run newFC (m.take (measurementCount C105Research.F)) s =
      scatterState keepC vs (run C105Research.F (m.take (measurementCount C105Research.F)) s) := by
    have h := CacheBetweenFrameResearch.forward (C105Research.head ++ C105LowEraseResearch.clear) C105Research.top
      27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide) keepC_geometry.1
      (fun q hq bad => C105Research.geometry.2.2 q (keepC_sub q hq) (by clear * - bad; simp only [C105Research.domain, List.mem_cons, List.mem_append] at bad ⊢; tauto))
      (fun q hq => C105Research.rawF_off q (keepC_sub q hq)) (fun q hq => C105Research.top_off q (keepC_sub q hq))
      s (m.take (measurementCount C105Research.F))
      (fun q hq => C105Research.prefix_zeroK s _ hz hb hi ha zero q (keepSubK q hq))
    rw [fwdVal] at h; exact h
  have mid := C105Research.middle_erased s m hz hb hi ha after flag
  have cacheEq : run (newFC ++ C105Research.M ++ newIC) m s = run (C105Research.F ++ C105Research.M ++ C105Research.I) m s := by
    apply CacheFromCleanForwardResearch.equivalent C105Research.F newFC C105Research.M C105Research.I newIC keepC vs
      fwdM (fun q hq => C105Research.middle_fresh q (keepC_sub q hq))
      (fun q hq => C105Research.I_off q (keepC_sub q hq)) keepC_geometry.1 s m
      (fun q hq => C105Research.forward_zeroK s _ hz hb hi ha zero q (keepSubK q hq)) forward
    rw [mid]
    let ms := middleState C105Research.oldF C105Research.oldM s m
    let mr := m.drop (measurementCount C105Research.F + measurementCount C105Research.M)
    let t := scatterState keepC vs (C105LowEraseResearch.erase ms)
    have comm : run C105Research.preInv mr t = scatterState keepC vs (C105LowEraseResearch.erase (run C105Research.preInv mr ms)) := by
      rw [show t = scatterState keepC vs (C105LowEraseResearch.erase ms) from rfl,
        run_scatter C105Research.preInv keepC vs _ _ (fun q hq => C105Research.preInv_off q (keepC_sub q hq)),
        C105LowEraseResearch.commute C105Research.preInv mr ms (fun q hq => C105Research.preInv_off q (C105Research.low_hosts q hq))]
    have bits (q : Wire) (hq : q ∈ C105Research.domain) : (run C105Research.preInv mr t).basis q = (run C105Research.preInv mr ms).basis q := by
      rw [comm, scatter_outside keepC vs _ q (fun bad => C105Research.geometry.2.2 q (keepC_sub q bad) hq)]
      exact C105LowEraseResearch.bit_same _ q (C105Research.domain_away_low q hq)
    have regs (r : List Wire) (sub : ∀ q ∈ r, q ∈ C105Research.domain) :
        regValue r (run C105Research.preInv mr t).basis = regValue r (run C105Research.preInv mr ms).basis :=
      regValue_congr _ _ _ (fun q hq => bits q (sub q hq))
    have rr := C105Research.pre_raw_ready H ms mr after
    have saved : keepC.map t.basis = vs := scatter_saved_map keepC vs _ keepC_geometry.1
      (by simp only [vs, ReorderedCacheBits.values, List.length_map, keepC_geometry.2.1, List.length_range])
    have same : keepC.map (run C105Research.preInv mr t).basis = keepC.map t.basis :=
      List.map_congr_left (fun q hq => run_preserves_outside C105Research.preInv mr t q (C105Research.preInv_off q (keepC_sub q hq)))
    simp only [newIC, C105Research.I, C105Research.rawI, ControlledBorrowResearch.run_cat]
    exact ReorderedConsumedSub.frame 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide)
      (by rw [C105Research.raw_lengths.1, C105Research.raw_lengths.2.1])
      (by rw [C105Research.raw_lengths.2.1, C105Research.raw_lengths.2.2])
      C105Research.raw_nd keepC_geometry.1 keepC_geometry.2.1 (fun q hq => C105Research.geometry.2.2 q (keepC_sub q hq))
      (run C105Research.preInv mr t) _ (fun q hq => (bits q (C105Research.c_in q hq)).trans (rr.1 q hq))
      ((bits _ C105Research.cin_in).trans rr.2.1) H (976 * H / 1024)
      ((regs _ C105Research.x_in).trans rr.2.2.1) ((regs _ C105Research.y_in).trans rr.2.2.2) (same.trans saved)
  have eq := ClearContextResearch.append_at (newFC ++ C105Research.M ++ newIC)
    (C105Research.F ++ C105Research.M ++ C105Research.I) (C105LowEraseResearch.clear ++ C105Research.tail) s m
    (by simp only [measurementCount_append, fwdM, invM]) cacheEq
  have shape : (C105Research.F ++ C105Research.M ++ C105Research.I) ++ (C105LowEraseResearch.clear ++ C105Research.tail) =
      C105Research.F ++ C105Research.M ++ (C105Research.I ++ C105LowEraseResearch.clear ++ C105Research.tail) := by
    have g (A B C D E : Program) : (A ++ B ++ C) ++ (D ++ E) = A ++ B ++ (C ++ D ++ E) := by simp only [List.append_assoc]
    exact g _ _ _ _ _
  exact eq.trans ((congrArg (fun P => run P m s) shape).trans (C105Research.plain_loop s m hz hb hi ha after flag))

private theorem coreC_frame (base : BasisState) (hc : C163Low4Middle.L.PairClean base)
    (hp : base C163Low4Middle.p = false) (hd : base C163Low4Middle.d = false) (O : Nat) (hO : O < SquareReduction.p) :
    Triple (SquareFrame C163Low4Middle.L.core.out base O) coreC
      (SquareFrame C163Low4Middle.L.core.out base
        (((if base C163Low4Middle.g then C163Low4Facts.Klow - C163Fold.payload C163Low4Middle.L base
           else C163Fold.payload C163Low4Middle.L base) + (SquareReduction.p - 1 - O)) % SquareReduction.p)) := by
  intro s m hf
  have len := C163Low4Middle.lengths; have fit := C163Low4Middle.fits
  have clean := C163Low4Middle.L.squareFrame_clean C163Low4Middle.hn base s.basis O hf hc
  have hz : ∀ u ∈ C163Low4Middle.pad, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
  have hb : ∀ u ∈ C163Low4Middle.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
  have ha : regValue C163Low4Middle.ga s.basis = 0 := C163Low4Ghost.ghostAcc_zero C163Low4Middle.L s.basis clean
  have zeroU : ∀ u ∈ C163Low4Middle.hs, s.basis u = false := StairSqLoopC.hs_zero base hc hd O s hf
  have zeroOld : ∀ u ∈ ReorderedCFixed.hosts, s.basis u = false := by
    have qz : s.basis C163Low4Middle.q = false := (regValue_zero _ _).mp clean.work C163Low4Middle.q (by decide)
    have rz : s.basis C163Low4Middle.r = false := (regValue_zero _ _).mp clean.work C163Low4Middle.r (by decide)
    have pz : s.basis C163Low4Middle.p = false := (hf.2 C163Low4Middle.p (by decide)).trans hp
    intro u hu; simp only [ReorderedCFixed.hosts, List.mem_cons] at hu
    rcases hu with rfl | rfl | rfl | hu; exact qz; exact rz; exact pz; exact zeroU u hu
  have offHs : ∀ u ∈ C163Low4Middle.hs, u ∉ wires (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) :=
    fun u hu => (ReorderedCFixed.off_plain u (StairSqLoopC.hosts_of_hs u hu)).1
  have goodOld := fun record => C163Low4Middle.good base hc O hO s record hf
  have goodSpecial : WReady C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
      (regValue C163Low4Middle.src s.basis)
      (middleState (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) C163Low4Middle.specialChecked.out s m) := by
    rw [ReorderedRetape.c_middle_eq C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
      C163Low4Middle.specialChecked.out len.1 len.2.2.2 fit s m hz hb clean.cin ha]
    exact goodOld _
  have middleEq := C163Low4Middle.bank_cert.middle_eq C163Low4Middle.hs C163Low4Middle.specialChecked.out C163Low4Middle.bankChecked.out
    (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) s m zeroU offHs
  have knownEq := CKKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
  have goodKnown : WReady C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
      (regValue C163Low4Middle.src s.basis)
      (middleState (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) KnownCMidStaged.body s m) := by
    rw [knownEq, middleEq]; exact goodSpecial
  have buildFrame := ReorderedCPlain.build_triple C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
    len.1 len.2.2.2 fit s.basis hz hb clean.cin s
    (m.take (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src))) ⟨ha, fun _ _ => rfl⟩
  have flag : (run (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
      (m.take (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src))) s).basis 4762 = false :=
    (buildFrame.2.2 4762 (by simp only [C163Low4Middle.ga, C163Low4Middle.pad, C163Low4Middle.bank, C163Low4Middle.src, C163Low4Middle.L, C163Middle.L, show Baselines.layout.dialogStreamedSquareWide = K0 from rfl, K0_eq]; decide +kernel)).trans clean.modFlag
  have plainNew := core_plainC s m hz hb clean.cin ha zeroOld goodKnown flag
  have midEq : run KnownCMidStaged.body (m.drop (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)))
      (run (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) m s) =
      run C163Low4Middle.bankChecked.out (m.drop (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)))
      (run (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) m s) := by
    simpa only [middleState, run_take] using knownEq
  have ctxt := ReorderedKnownA.context_eq (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
    C163Low4Middle.bankChecked.out KnownCMidStaged.body (ReorderedCPlain.unbuild C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
    s m CKKnownMiddleResearch.measurements midEq
  have middleReplace := C163Low4Middle.bank_cert.surround_eq C163Low4Middle.hs C163Low4Middle.specialChecked.out C163Low4Middle.bankChecked.out
    (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
    (ReorderedCPlain.unbuild C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) s m zeroU offHs
  have plainEq := ReorderedRetape.c_loop_eq C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src C163Low4Middle.specialChecked.out
    len.1 len.2.2.2 fit s m hz hb clean.cin ha goodOld
  let record := ReorderedRetape.tape (measurementCount (C163NarrowAcc.build8 C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src))
    (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)) m
  have oldFrame := C163Low4Middle.frame base hc hp hd O hO s record hf
  rw [C163Low4Middle.eq_plain base hc hp hd O hO s record hf] at oldFrame
  exact ReorderedCFixed.transport _ s _ _ (plainNew.trans (ctxt.trans (middleReplace.trans plainEq))) oldFrame

private theorem keepC_cached_wires : wires rawFC ⊆ C105Research.domain.toFinset ∪ keepC.toFinset :=
  (ReorderedSupport.cached 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
    (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
    (by rw [C105Research.raw_lengths.2.2]; decide)
    (by rw [C105Research.raw_lengths.1, C105Research.raw_lengths.2.1])
    (by rw [C105Research.raw_lengths.2.1, C105Research.raw_lengths.2.2])).1

private theorem keepC_consumed_wires :
    wires (ReorderedConsumedSub.consumed 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin) ⊆
      C105Research.domain.toFinset ∪ keepC.toFinset :=
  ReorderedSupport.consumed 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
    (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
    (by rw [C105Research.raw_lengths.2.2]; decide)
    (by rw [C105Research.raw_lengths.1, C105Research.raw_lengths.2.1])
    (by rw [C105Research.raw_lengths.2.1, C105Research.raw_lengths.2.2])

theorem loopPCC_off (h : Wire) (hh : h ∈ ReorderedCFixed.hosts) (hk : h ∉ keepC) : h ∉ wires loopPCC := by
  have hA : h ∈ C105Research.hosts := List.mem_append.mpr (Or.inl hh)
  have hb : h ∉ wires (ReorderedCPlain.build C105PrefixResearch.acc C105PrefixResearch.pad
      C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src) := (ReorderedCFixed.off_plain h hh).1
  rw [C105Research.plain_split] at hb
  simp only [wires_append, Finset.mem_union, not_or] at hb
  have ht : h ∉ wires (ReorderedCPlain.unbuild C105PrefixResearch.acc C105PrefixResearch.pad
      C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src) := (ReorderedCFixed.off_plain h hh).2
  rw [C105Research.unbuild_split] at ht
  simp only [wires_append, Finset.mem_union, not_or] at ht
  have clearOff : h ∉ wires C105LowEraseResearch.clear := by
    rw [StairSqLoopC.clear_wires]; intro bad
    exact C105Research.old_away h hh ((by decide : ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire) ⊆ C105Research.ports) (List.mem_toFinset.mp bad))
  have out : h ∉ C105Research.domain.toFinset ∪ keepC.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]; exact ⟨C105Research.geometry.2.2 h hA, hk⟩
  simp only [loopPCC, restC, newIC, wires_append, Finset.mem_union, not_or, and_assoc]
  exact ⟨fun bad => hb.1 (SignCHeadSupport.support bad), clearOff, fun bad => out (keepC_cached_wires bad),
    C105Research.top_off h hA, C105Research.middle_fresh h hA, C105Research.preInv_off h hA,
    fun bad => out (keepC_consumed_wires bad), clearOff, ht.2⟩

theorem loopPCC_support : wires loopPCC ⊆ C105Research.S := by
  have hh : wires SignCHead.head ⊆ C105Research.S := by
    apply Finset.Subset.trans ?_ C105Research.old_prefix_support
    rw [C105Research.oldPrefix, wires_append]
    exact Finset.subset_union_left
  have ks : C105Research.domain.toFinset ∪ keepC.toFinset ⊆ C105Research.S := by
    intro q hq; apply C105Research.raw_domain_in
    simp only [Finset.mem_union, List.mem_toFinset] at hq ⊢
    rcases hq with h | h; exact Or.inl h; exact Or.inr (keepC_sub q h)
  simp only [loopPCC, restC, newIC, wires_append, Finset.union_subset_iff]
  exact ⟨hh,
    ⟨⟨⟨⟨⟨⟨C105Research.clear_support, keepC_cached_wires.trans ks⟩, C105Research.endpoint_support.1⟩,
      C105Research.middle_support⟩, ⟨C105Research.endpoint_support.2.1, keepC_consumed_wires.trans ks⟩⟩,
      C105Research.clear_support⟩, C105Research.endpoint_support.2.2⟩⟩

theorem loopPCC_physical : GatePhysical loopPCC := by
  have f := ReorderedPhysical.cached 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
    (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
    (by rw [C105Research.raw_lengths.2.2]; decide)
    C105Research.raw_nd (fun q hq bad => C105Research.geometry.2.2 q (keepC_sub q hq) (C105Research.c_in q bad))
  have n := notRegister_physical C105Research.ys
  simp only [loopPCC, restC, newIC, ReorderedConsumedSub.consumed, gatePhysical_append]
  exact ⟨SignCHeadResources.physical,
    ⟨⟨⟨⟨⟨⟨C105LowEraseResearch.physical, f.1⟩, C105Research.endpoint_physical.1⟩,
      CKAliasesResearch.physical⟩, ⟨C105Research.endpoint_physical.2.1, ⟨⟨n, f.2⟩, n⟩⟩⟩,
      C105LowEraseResearch.physical⟩, C105Research.endpoint_physical.2.2⟩⟩

theorem loopC_pairs_free : ∀ ab ∈ StairSqLoopC.pairs hs, ab.2 ∉ wires loopPCC := by
  intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
  apply loopPCC_off _ (StairSqLoopC.hosts_of_hs _ (StairSqLoopC.holes_geometry44.2.2 y hy))
  have h := List.idxOf_lt_length_of_mem hy; rw [StairSqLoopA.hostDomain_length44] at h
  exact keepC_geometry.2.2.2.2.1 _ h

theorem loopC_support : wires loopC ⊆ C105Research.S := by
  intro q hq
  have sub := hostRename_support (StairSqLoopC.pairs hs) loopPCC (StairSqLoopC.pairs_nodup44 hs (List.Sublist.refl _)) loopC_pairs_free hq
  rcases Finset.mem_union.mp sub with h | h
  · exact loopPCC_support (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopC.pairs_snd] at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact C105Research.raw_domain_in (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (StairSqLoopC.hosts_of_hs _ (StairSqLoopC.holes_geometry44.2.2 y hy))))))

theorem loopC_avoids_hs : ∀ q ∈ hs, q ∉ wires loopC := by
  intro q hq
  have h := hostRename_avoids (StairSqLoopC.pairs hs) loopPCC (StairSqLoopC.pairs_nodup44 hs (List.Sublist.refl _)) loopC_pairs_free
  rw [StairSqLoopC.pairs_fst] at h; exact h q hq

theorem loopC_avoids_workTC : ∀ q ∈ workTC, q ∉ wires loopC := by
  intro q hq bad
  have sub := hostRename_support (StairSqLoopC.pairs hs) loopPCC (StairSqLoopC.pairs_nodup44 hs (List.Sublist.refl _)) loopC_pairs_free bad
  rcases Finset.mem_union.mp sub with h | h
  · have hm : ∀ x ∈ workTC, x ∈ ReorderedCFixed.hosts := by rw [workTC_lit, hostsCFix_fast]; decide +kernel
    exact loopPCC_off q (hm q hq) (keepC_geometry.2.2.2.1 q hq) (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopC.pairs_snd] at h
    have dis : ∀ x ∈ workTC, x ∉ hs.map StairSqLoopC.hostOf := by simp only [workTC_lit, StairSqLoopC.hostOf, show StairSqLoopA.hostDomain = hs from rfl, hs_lit, hsC_fast]; decide +kernel
    exact dis q hq (List.mem_toFinset.mp h)

theorem loopC_counts :
    toffoliCount loopC = toffoliCount C105SignResearch.loop + 81 ∧
    measurementCount loopC = measurementCount C105SignResearch.loop := by
  have hr := hostRename_counts (StairSqLoopC.pairs hs) loopPCC
  have rel : toffoliCount loopPCC + 27 = toffoliCount StairSqLoopC.loopNC ∧
      measurementCount loopPCC = measurementCount StairSqLoopC.loopNC := by
    have cb := ReorderedGenericCache.count_balance 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide) (by rw [C105Research.raw_lengths.2.2]; decide)
    rw [loopPCC, restC, rawFC, newIC, StairSqLoopC.loopNC, StairSqLoopC.suffixNC,
      C105Research.I, C105Research.rawI, C105Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [toffoliCount_append, measurementCount_append]
    exact ⟨by omega, by omega⟩
  have nc := StairSqLoopC.loopNC_counts
  rw [loopC, hr.1, hr.2]
  exact ⟨by omega, by omega⟩

theorem loopC_slots : Challenge.gateSlots loopC = Challenge.gateSlots C105SignResearch.loop + 237 := by
  have hr := hostRename_slots (StairSqLoopC.pairs hs) loopPCC
  have rel : Challenge.gateSlots loopPCC + 81 = Challenge.gateSlots StairSqLoopC.loopNC := by
    have sc := ReorderedSlots.cache 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide) keepC_geometry.2.1
    rw [loopPCC, restC, rawFC, newIC, StairSqLoopC.loopNC, StairSqLoopC.suffixNC,
      C105Research.I, C105Research.rawI, C105Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [Challenge.gateSlots_append]
    omega
  have nc := StairSqLoopC.loopNC_slots
  rw [loopC, hr]
  omega

theorem loopC_frame : C105SignResearch.DirectLoopFrame loopC := by
  have pcFrame : C105SignResearch.DirectLoopFrame loopPCC := by
    intro base hc hp hd O hO s m hf
    have clean := C163Low4Middle.L.squareFrame_clean C163Low4Middle.hn base s.basis O hf hc
    have hz : ∀ u ∈ C163Low4Middle.pad, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
    have hb : ∀ u ∈ C163Low4Middle.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
    have ha : regValue C163Low4Middle.ga s.basis = 0 := C163Low4Ghost.ghostAcc_zero C163Low4Middle.L s.basis clean
    have hhead : ∀ a b : List Bool, run SignCHead.head a s = run (ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) b s :=
      fun a b => ReorderedFrameUnique.program_eq C163Low4Middle.ga s.basis 0 ((2 ^ 140 - 48 * regValue C163Low4Middle.src s.basis) % 2 ^ 140) _ _
        (SignCHead.frame s.basis hz hb clean.cin)
        (ReorderedCHead.head_triple C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src C163Low4Middle.lengths.1 C163Low4Middle.lengths.2.2.2.le C163Low4Middle.fits s.basis hz hb clean.cin)
        s a b ⟨ha, fun _ _ => rfl⟩
    have eq := SignRetape.replace SignCHead.head (ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) restC s m hhead
    have hheadEq : C105Research.head = ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src := rfl
    have hcoreEq : coreC = ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src ++ restC := by
      rw [coreC, newFC, restC, hheadEq]
      have g (A B C D E F G H : Program) : (((A ++ B ++ C ++ D) ++ E ++ F) ++ (G ++ H)) = A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H) := by simp only [List.append_assoc]
      exact g _ _ _ _ _ _ _ _
    have eq' : run loopPCC m s = run coreC (SignRetape.tape SignCHead.head (ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) m) s := by
      rw [loopPCC, hcoreEq]; exact eq
    exact ReorderedCFixed.transport _ s _ _ eq' (coreC_frame base hc hp hd O hO s _ hf)
  intro base hc hp hd O hO s m hf
  have r := pcFrame base hc hp hd O hO s m hf
  have hEq : run loopC m s = run loopPCC m s := by
    apply hostRename_run_eq (StairSqLoopC.pairs hs) loopPCC s m
    · intro ab hab; obtain ⟨y, hy, hyab⟩ := List.mem_map.mp hab
      have hfst : ab.1 = y := by rw [← hyab]
      rw [hfst]
      have hg := StairSqLoopC.holes_geometry44.2.1 y hy
      exact (hf.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact StairSqLoopC.hs_zero base hc hd O s hf _ (StairSqLoopC.holes_geometry44.2.2 y hy)
    · intro ab hab
      obtain ⟨y, hy, e⟩ := List.mem_map.mp hab
      have first : ab.1 = y := by rw [← e]
      rw [first]
      have hg := StairSqLoopC.holes_geometry44.2.1 y hy
      exact (r.2.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · exact loopC_pairs_free
  rw [hEq]; exact r

theorem bodyC_wires_plain : wires bodyC ⊆ wires bodyCPlain ∪ (K0.core.pad.take 34).toFinset := by
  have sp := directFold_rename_support foldPairsC (negRot K0) (negRot_count K0) foldPairsC_geom.1 (fun ab hab => (foldPairsC_geom.2.2.2.1 ab hab).2.2.1)
  rw [foldPairsC_geom.2.2.1] at sp
  intro q hq
  simp only [bodyC, wires_append, Finset.mem_union] at hq
  rcases hq with (b | b) | b
  · rcases Finset.mem_union.mp (sp b) with h | h
    · exact Finset.mem_union_left _ (by simp only [bodyCPlain, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, wires_append, Finset.mem_union]; left; left; exact (Finset.mem_sdiff.mp h).1)
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (by simp only [bodyCPlain, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, wires_append, Finset.mem_union]; left; right; exact b)
  · exact Finset.mem_union_left _ (by simp only [bodyCPlain, C105SignResearch.directBody, wires_append, Finset.mem_union]; right; exact b)

theorem bodyC_ok : BodyCOK bodyC := by
  have s0 : wires bodyCPlain ⊆ insert D0 (G0 :: K0.wires).toFinset := by
    have h := C105SignResearch.direct_body_coarse_S loopC loopC_support
    rw [lc_eq_K0] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro q hq; rcases Finset.mem_union.mp (bodyC_wires_plain hq) with h | h
    · exact s0 h
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsC_geom.2.2.2.2 q (by rw [foldPairsC_geom.2.2.1]; exact List.mem_toFinset.mp h)).2.1))
  · intro base M hP hc hg hd O hO s m hf
    have rawRef := C105SignResearch.direct_body_frame loopC loopC_frame base M hP hc hg hd O hO s m hf
    have views := accC_views K0 hwK base M hP
    have hv : K0.MeasuredFoldView base (negRot K0) := views (.inl (negRot K0)) (by simp [accCMix])
    have mc : measurementCount dFC = measurementCount (directFoldQTq K0 (negRot K0)) := (hostRename_counts foldPairsC (directFoldQTq K0 (negRot K0))).2
    have eq1 : run dFC m s = run (directFoldQTq K0 (negRot K0)) m s :=
      directFold_rename_run foldPairsC (negRot K0) (negRot_count K0) (negRot_length K0 hwK) rfl rfl
        (fun ab hab => ⟨(foldPairsC_geom.2.2.2.1 ab hab).1, (foldPairsC_geom.2.2.2.1 ab hab).2.1⟩)
        (fun ab hab => ⟨(foldPairsC_geom.2.2.2.1 ab hab).2.2.1, (foldPairsC_geom.2.2.2.1 ab hab).2.2.2.1⟩)
        base hv hc O hO s m hf
    have bodyEq : run bodyC m s = run bodyCPlain m s := by
      simp only [bodyC, bodyCPlain, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
        ControlledBorrowResearch.run_cat, measurementCount_append, mc]
      rw [eq1]
    rw [bodyEq]; exact rawRef

theorem bodyC_avoids_workTC : ∀ q ∈ workTC, q ∉ wires bodyC := by
  intro q hq bad
  have hn := (List.nodup_cons.mp controlND).2
  have a1 := hostRename_avoids foldPairsC (directFoldQTq K0 (negRot K0)) foldPairsC_geom.1
    (fun ab hab => directFoldQ_free K0 hn (negRot K0) (negRot_count K0) ab.2 (by simp [directFree, (foldPairsC_geom.2.2.2.1 ab hab).2.2.1]))
  rw [foldPairsC_geom.2.1] at a1
  simp only [bodyC, wires_append, Finset.mem_union] at bad
  rcases bad with (b | b) | b
  · exact a1 q hq b
  · exact loopC_avoids_workTC q hq b
  · exact (by rw [workTC_lit, K0_eq]; decide +kernel : ∀ x ∈ workTC, x ≠ K0.core.cin) q hq (Finset.mem_singleton.mp (padding_wires 7 K0.core.cin b))

theorem bodyC_avoids_hs : ∀ q ∈ hs, q ∉ wires bodyC := by
  intro q hq bad
  rcases Finset.mem_union.mp (bodyC_wires_plain bad) with h | h
  · exact C105SignResearch.direct_body_holes loopC hs (fun x hx => (StairSqLoopC.holes_geometry44.2.1 x hx).1) loopC_avoids_hs q hq h
  · exact (foldPairsC_geom.2.2.2.2 q (by rw [foldPairsC_geom.2.2.1]; exact List.mem_toFinset.mp h)).1 hq

theorem bodyC_physical : GatePhysical bodyC := by
  have p0 := C105SignResearch.direct_body_physical loopC (hostRename_physical _ _ loopPCC_physical)
  simp only [C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, gatePhysical_append] at p0
  simp only [bodyC, dFC, gatePhysical_append]
  exact ⟨⟨hostRename_physical _ _ p0.1.1, p0.1.2⟩, p0.2⟩

theorem bodyC_counts :
    toffoliCount bodyC = toffoliCount C105SignResearch.body + 81 ∧
    measurementCount bodyC = measurementCount C105SignResearch.body := by
  have c0 := C105SignResearch.direct_body_counts loopC
  have cl := loopC_counts
  have r1 := hostRename_counts foldPairsC (directFoldQTq K0 (negRot K0))
  have eqT : toffoliCount bodyC = toffoliCount (C105SignResearch.directBody loopC) := by
    simp only [bodyC, dFC, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
      toffoliCount_append, r1.1]
  have eqM : measurementCount bodyC = measurementCount (C105SignResearch.directBody loopC) := by
    simp only [bodyC, dFC, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
      measurementCount_append, r1.2]
  rw [eqT, eqM]
  exact ⟨by omega, by omega⟩

theorem bodyC_slots : Challenge.gateSlots bodyC + 275 = Challenge.gateSlots C105SignResearch.body := by
  have s0 := C105SignResearch.direct_body_slots loopC
  have sl := loopC_slots
  have r1 := hostRename_slots foldPairsC (directFoldQTq K0 (negRot K0))
  have eqS : Challenge.gateSlots bodyC = Challenge.gateSlots (C105SignResearch.directBody loopC) := by
    simp only [bodyC, dFC, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
      Challenge.gateSlots_append, r1]
  rw [eqS]
  omega

theorem bodyCPlain_fine :
    wires bodyCPlain ⊆ insert C163Low4Middle.d
      (wires (OwnDiagAll12Square.bodyCKTq C163Low4Middle.L C163Low4Middle.g)) :=
  C105SignResearch.direct_body_fine_S loopC loopC_support

end BodyC

/-! ## Branch wrappers (`brC`, `brB`, `brA`) and top-level assembly -/

section Branches
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical LocalRebuild.improved directFoldQTq

/-- Generic parked-copy split-65 wrapper around any `SplitCfg` and body. -/
def withSplitPark (c : SplitCfg) (keepBits : Nat) (parkHosts : List Wire) (body : Program) : Program :=
  copyRegister (some G0) c.src c.bank ++
  c.make ++
  eraseMask G0 (c.src.take keepBits) (c.bank.take keepBits) ++
  ParkCopy.dummies parkHosts ++
  ParkCopy.move (c.bank.drop keepBits) parkHosts ++
  renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body) ++
  CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits) ++
  ParkCopy.move parkHosts (c.bank.drop keepBits) ++
  c.clear ++
  eraseMask G0 c.src c.bank

def brC : Program :=
  OwnDiagAll12Square.gPrep K0 ++
  withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC ++
  OwnDiagAll12Square.gClear K0

def brB : Program :=
  withSplitPark cfgB 119 (ParkCopy.hosts E0) bodyB

def brA : Program :=
  withSplitPark cfgA 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA

private theorem pull_swap_invol (a b : Wire) (s : State) :
    pullState (Equiv.swap a b) (pullState (Equiv.swap a b) s) = s := by
  apply State.extensionality
  · rfl
  · funext q; simp [pullState]

private theorem pull_swap_fix (a b : Wire) (s : State) (h : s.basis a = s.basis b) :
    pullState (Equiv.swap a b) s = s := by
  apply State.extensionality
  · rfl
  · funext q
    simp only [pullState, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; exact h.symm
    · subst h2; exact h
    · rfl

private theorem swap_run_eq (a b : Wire) (P : Program) (s : State) (m : List Bool)
    (h0 : s.basis a = s.basis b) (h1 : (run P m s).basis a = (run P m s).basis b) :
    run (renameProgram (Equiv.swap a b) P) m s = run P m s := by
  have hr := ECDSAAdd.run_rename (Equiv.swap a b) (Equiv.swap a b).injective P m s
  rw [pull_swap_fix a b s h0] at hr
  have h2 := congrArg (pullState (Equiv.swap a b)) hr
  rw [pull_swap_invol, pull_swap_fix a b (run P m s) h1] at h2
  exact h2

private theorem state_eq_of_out (u v : State) (hp : u.phase = v.phase)
    (ho : regValue K0.core.out u.basis = regValue K0.core.out v.basis)
    (hf : ∀ q, q ∉ K0.core.out → u.basis q = v.basis q) : u = v := by
  apply State.extensionality _ _ hp
  funext q
  by_cases hq : q ∈ K0.core.out
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    have h1 := RawClearCarryProbe.register_bit K0.core.out i u.basis hi
    have h2 := RawClearCarryProbe.register_bit K0.core.out i v.basis hi
    have hg : K0.core.out.getD i 0 = K0.core.out[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hg] at h1 h2
    rw [h1, h2, ho]
  · exact hf q hq

private theorem even_bit0_false (r : List Wire) (b : BasisState) (k : Nat)
    (hr : 0 < r.length) (hv : regValue r b = 2 * k) : b (r.getD 0 0) = false := by
  have hb := RawClearCarryProbe.register_bit r 0 b hr
  rw [hv] at hb
  simpa using hb

private theorem hi_bit_false (r : List Wire) (b : BasisState) (i : Nat)
    (hi : i < r.length) (hlt : regValue r b < 2 ^ i) : b (r.getD i 0) = false := by
  have hb := RawClearCarryProbe.register_bit r i b hi
  have hdiv : regValue r b / 2 ^ i = 0 := Nat.div_eq_of_lt hlt
  rw [hdiv] at hb
  simpa using hb

/-- Core correctness theorem for `withSplitPark` when `body` avoids `E0` and `c.workT`. -/
private theorem withSplitPark_correct (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program) (V : Nat)
    (hkLen : keepBits + parkHosts.length = c.n)
    (hkPos : 0 < keepBits)
    (hsrcLen : c.src.length = c.n)
    (hParkNd : parkHosts.Nodup)
    (hParkIn : ∀ h ∈ parkHosts, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0)
    (hParkDisBank : ∀ h ∈ parkHosts, h ∉ c.bank)
    (hParkDisSrc : ∀ h ∈ parkHosts, h ∉ c.src)
    (hParkDisDst : ∀ h ∈ parkHosts, h ∉ c.dst)
    (hParkDisOut : ∀ h ∈ parkHosts, h ∉ K0.core.out)
    (hParkDisG0 : G0 ∉ parkHosts)
    (hParkDisSw : ∀ h ∈ parkHosts, h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478)
    (hSrcDis : (G0 :: c.src ++ c.bank).Nodup)
    (hE0DisBank : ∀ q ∈ E0, q ∉ c.bank)
    (hWorkTSub : ∀ q ∈ c.workT, q ∈ K0.core.work ∨ q = D0)
    (hBodyDisE0 : ∀ q ∈ E0, q ∉ wires body)
    (hBodyDisWorkT : ∀ q ∈ c.workT, q ∉ wires body)
    (hBodyDisEU : ControlLoan1589BFFold.eU K0 ∈ parkHosts → ControlLoan1589BFFold.eU K0 ∉ wires body)
    (hLiveSub : ∀ q ∈ c.liveT, q ∈ E0 ∨ q ∈ c.workT)
    (hLiveDisBank : ∀ q ∈ c.liveT, q ∉ c.bank)
    (hLiveDisSrc : ∀ q ∈ c.liveT, q ∉ c.src)
    (hLiveDisOut : ∀ q ∈ c.liveT, q ∉ K0.core.out)
    (hScSub : ∀ q ∈ c.cleanScratch, q ∈ K0.foldPad ∨ q ∈ K0.core.work)
    (hScDisBank : ∀ q ∈ c.cleanScratch, q ∉ c.bank)
    (hScDisSrc : ∀ q ∈ c.cleanScratch, q ∉ c.src)
    (hScDisOut : ∀ q ∈ c.cleanScratch, q ∉ K0.core.out)
    (hScDisPark : ∀ q ∈ c.cleanScratch, q ∉ parkHosts)
    (hDstDisBank : ∀ q ∈ c.dst, q ∉ c.bank)
    (hDstDisSrc : ∀ q ∈ c.dst, q ∉ c.src)
    (hDstDisOut : ∀ q ∈ c.dst, q ∉ K0.core.out)
    (hBankDisOut : ∀ q ∈ c.bank, q ∉ K0.core.out)
    (hSrcDisOut : ∀ q ∈ c.src, q ∉ K0.core.out)
    (hG0Out : G0 ∉ c.bank ∧ G0 ∉ c.dst ∧ G0 ∉ c.liveT ∧ G0 ∉ c.cleanScratch ∧ G0 ∉ K0.core.out)
    (hCacheEq : LowZero18Square.cacheWire K0 c.dst = c.dst.headD 0)
    (hParkZeroAfterMake : ∀ s0 : State, ∀ m0 : List Bool,
      regValue c.dst s0.basis = 0 → regValue c.liveT s0.basis = 0 →
      regValue c.cleanScratch s0.basis = 0 → s0.basis K0.core.cin = false →
      (ControlLoan1589BFFold.eU K0 ∈ parkHosts → s0.basis (ControlLoan1589BFFold.eU K0) = false) →
      (∀ q ∈ E0, s0.basis q = false) →
      (∀ h ∈ parkHosts, (run c.make m0 s0).basis h = false) ∧
      (run c.make m0 s0).basis 5093 = false ∧ (run c.make m0 s0).basis 5478 = false)
    (s : State) (records : List Bool) (hc : K0.PairClean s.basis)
    (hd0 : regValue c.dst s.basis = 0) (he0 : regValue E0 s.basis = 0)
    (hd0_bit : s.basis D0 = false)
    (heu0 : ControlLoan1589BFFold.eU K0 ∈ parkHosts → s.basis (ControlLoan1589BFFold.eU K0) = false)
    (callback : ∀ t : State, ∀ m : List Bool,
      regValue c.dst t.basis = (if s.basis G0 then regValue c.src s.basis else 0) ^ 2 →
      (∀ q, q ∉ c.dst → t.basis q = s.basis q) →
      (run body m t).phase = t.phase ∧ regValue K0.core.out (run body m t).basis = V ∧
      ∀ q, q ∉ K0.core.out → (run body m t).basis q = t.basis q) :
    (run (withSplitPark c keepBits parkHosts body) records s).phase = s.phase ∧
    regValue K0.core.out (run (withSplitPark c keepBits parkHosts body) records s).basis = V ∧
    ∀ q, q ∉ K0.core.out → (run (withSplitPark c keepBits parkHosts body) records s).basis q = s.basis q := by
  have hbankLen : c.bank.length = c.n := v.bankLen
  have hsrc_bank : c.src.length = c.bank.length := by omega
  have hkeepLe : keepBits ≤ c.n := by omega
  have hE0_all : ∀ q ∈ E0, s.basis q = false := (regValue_zero _ _).mp he0
  have hWork_all : ∀ q ∈ K0.core.work, s.basis q = false := (regValue_zero _ _).mp hc.work
  have hPad_all : ∀ q ∈ K0.foldPad, s.basis q = false := (regValue_zero _ _).mp hc.pad
  have hSc0_s : regValue c.cleanScratch s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (hScSub q hq).elim (hPad_all q) (hWork_all q))
  have hLive0_s : regValue c.liveT s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (hLiveSub q hq).elim (hE0_all q) (fun hw => (hWorkTSub q hw).elim (hWork_all q) (fun h => h ▸ hd0_bit)))
  have hSwMem : (4834 : Wire) ∈ K0.foldPad ∧ (4875 : Wire) ∈ K0.foldPad ∧
      (4834 : Wire) ∉ K0.core.out ∧ (5093 : Wire) ∉ K0.core.out ∧
      (4875 : Wire) ∉ K0.core.out ∧ (5478 : Wire) ∉ K0.core.out ∧
      (4834 : Wire) ∉ allowedWires ∧ (4875 : Wire) ∉ allowedWires :=
    have h6 : (4834 : Wire) ∈ K0.foldPad ∧ (4875 : Wire) ∈ K0.foldPad ∧
        (4834 : Wire) ∉ K0.core.out ∧ (5093 : Wire) ∉ K0.core.out ∧
        (4875 : Wire) ∉ K0.core.out ∧ (5478 : Wire) ∉ K0.core.out := by rw [K0_eq]; decide +kernel
    ⟨h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, h6.2.2.2.2.1, h6.2.2.2.2.2, not_mem_allowedWires_4834, not_mem_allowedWires_4875⟩
  have h4834_0 : s.basis 4834 = false := hPad_all 4834 hSwMem.1
  have h4875_0 : s.basis 4875 = false := hPad_all 4875 hSwMem.2.1
  have h4834_notReal : (4834 : Wire) ∉ c.realAll := fun h => hSwMem.2.2.2.2.2.2.1 (v.realAllowed _ h)
  have h4875_notReal : (4875 : Wire) ∉ c.realAll := fun h => hSwMem.2.2.2.2.2.2.2 (v.realAllowed _ h)
  have h5093_notBank : (5093 : Wire) ∉ c.bank := hE0DisBank 5093 (by rw [E0_eq]; decide +kernel)
  have h5478_notBank : (5478 : Wire) ∉ c.bank := hE0DisBank 5478 (by rw [E0_eq]; decide +kernel)
  have hCin_notBank : K0.core.cin ∉ c.bank :=
    kdis v.realNd (r := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; simp only [List.count_cons, List.count_nil]; omega) _ (by simp)
  have hCin_notDst : K0.core.cin ∉ c.dst :=
    kdis v.realNd (r := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; simp only [List.count_cons, List.count_nil]; omega) _ (by simp)
  have hCin_notLive : K0.core.cin ∉ c.liveT :=
    kdis v.realNd (r := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append, List.count_cons, List.count_nil]; omega) _ (by simp)
  have hCin_notPark : K0.core.cin ∉ parkHosts := fun hp =>
    (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel : K0.core.cin ∉ E0 ∧ K0.core.cin ≠ ControlLoan1589BFFold.eU K0) |>
      fun h => (hParkIn _ hp).elim h.1 h.2
  have hCin_notOut : K0.core.cin ∉ K0.core.out := by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  have hParkDisReal : ∀ h ∈ parkHosts, h ∉ c.dst ∧ h ∉ c.bank := fun h hh => ⟨hParkDisDst h hh, hParkDisBank h hh⟩
  let P := if s.basis G0 then regValue c.src s.basis else 0
  let pA := copyRegister (some G0) c.src c.bank
  let pM := c.make
  let pE1 := eraseMask G0 (c.src.take keepBits) (c.bank.take keepBits)
  let pD := ParkCopy.dummies parkHosts
  let pMI := ParkCopy.move (c.bank.drop keepBits) parkHosts
  let pB := renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)
  let pC1 := CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits)
  let pMO := ParkCopy.move parkHosts (c.bank.drop keepBits)
  let pCL := c.clear
  let pE := eraseMask G0 c.src c.bank
  obtain ⟨r9, mE, eE⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1 ++ pMO ++ pCL) pE records s
  obtain ⟨r8, mCL, eCL⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1 ++ pMO) pCL r9 s
  obtain ⟨r7, mMO, eMO⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1) pMO r8 s
  obtain ⟨r6, mC1, eC1⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB) pC1 r7 s
  obtain ⟨r5, mB, eB⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI) pB r6 s
  obtain ⟨r4, mMI, eMI⟩ := kseq (pA ++ pM ++ pE1 ++ pD) pMI r5 s
  obtain ⟨r3, mD, eD⟩ := kseq (pA ++ pM ++ pE1) pD r4 s
  obtain ⟨r2, mE1, eE1⟩ := kseq (pA ++ pM) pE1 r3 s
  obtain ⟨mA, mM, eM⟩ := kseq pA pM r2 s
  rw [show withSplitPark c keepBits parkHosts body = pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1 ++ pMO ++ pCL ++ pE from rfl,
    eE, eCL, eMO, eC1, eB, eMI, eD, eE1, eM]
  -- 1. pA: copy controlled src into bank
  have hndSB : (c.src ++ c.bank).Nodup := (List.nodup_cons.mp hSrcDis).2
  have hG0B : ∀ x ∈ some G0, x ∉ c.bank := fun x hx => by
    cases Option.some.inj hx; exact hG0Out.1
  have hBank0_s : regValue c.bank s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => hWork_all q (List.mem_of_mem_take (List.mem_of_mem_take hq)))
  have stA := copyRegister_correct (some G0) c.src c.bank hsrc_bank hndSB hG0B s mA
  generalize hsA : run pA mA s = sA at stA ⊢
  have sA_bank : regValue c.bank sA.basis = P := by
    have h := stA.2.2
    rw [hBank0_s, Nat.zero_xor] at h
    simpa [P] using h
  have sA_out (q : Wire) (hb : q ∉ c.bank) : sA.basis q = s.basis q := stA.2.1 q hb
  have hTakeA : regValue (c.bank.take keepBits) sA.basis =
      if s.basis G0 = true then regValue (c.src.take keepBits) s.basis else 0 := by
    have eA := regValue_append (c.bank.take keepBits) (c.bank.drop keepBits) sA.basis
    rw [List.take_append_drop, sA_bank] at eA
    have eS := regValue_append (c.src.take keepBits) (c.src.drop keepBits) s.basis
    rw [List.take_append_drop] at eS
    have hlenT : (c.bank.take keepBits).length = keepBits := by simp [hbankLen, hkeepLe]
    have hlenS : (c.src.take keepBits).length = keepBits := by simp [hsrcLen, hkeepLe]
    have hltA : regValue (c.bank.take keepBits) sA.basis < 2 ^ keepBits := by
      simpa [hlenT] using regValue_lt (c.bank.take keepBits) sA.basis
    have hltS : regValue (c.src.take keepBits) s.basis < 2 ^ keepBits := by
      simpa [hlenS] using regValue_lt (c.src.take keepBits) s.basis
    cases hg : s.basis G0
    · simp only [P, hg, Bool.false_eq_true, if_false] at eA ⊢
      omega
    · simp only [P, hg, if_true] at eA ⊢
      rw [hlenT] at eA; rw [hlenS] at eS
      have m1 : regValue (c.bank.take keepBits) sA.basis = regValue c.src s.basis % 2 ^ keepBits := by
        rw [eA, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hltA]
      have m2 : regValue (c.src.take keepBits) s.basis = regValue c.src s.basis % 2 ^ keepBits := by
        rw [eS, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hltS]
      exact m1.trans m2.symm
  -- 2. pM: c.make computes dst = P^2 and liveT
  have sA_dst0 : regValue c.dst sA.basis = 0 := (regValue_congr _ _ s.basis (fun q hq => sA_out q (hDstDisBank q hq))).trans hd0
  have sA_live0 : regValue c.liveT sA.basis = 0 := (regValue_congr _ _ s.basis (fun q hq => sA_out q (hLiveDisBank q hq))).trans hLive0_s
  have sA_sc0 : regValue c.cleanScratch sA.basis = 0 := (regValue_congr _ _ s.basis (fun q hq => sA_out q (hScDisBank q hq))).trans hSc0_s
  have sA_cin0 : sA.basis K0.core.cin = false := (sA_out _ hCin_notBank).trans hc.cin
  have stM := cfg_make_correct c v sA mM sA_dst0 sA_live0 sA_sc0 sA_cin0
  have hZeros := hParkZeroAfterMake sA mM sA_dst0 sA_live0 sA_sc0 sA_cin0
    (fun hm => (sA_out _ (hParkDisBank _ hm)).trans (heu0 hm))
    (fun q hq => (sA_out q (hE0DisBank q hq)).trans (hE0_all q hq))
  generalize hsM : run pM mM sA = sM at stM hZeros ⊢
  have sM_dst : regValue c.dst sM.basis = P ^ 2 := by rw [stM.2.1, sA_bank]
  have sM_out (q : Wire) (hd : q ∉ c.dst) (hl : q ∉ c.liveT) : sM.basis q = sA.basis q := stM.2.2.2.2.2.2 q hd hl
  have hSrcDisBank : ∀ q ∈ c.src, q ∉ c.bank := fun q hq hb => (List.nodup_append.mp hndSB).2.2 q hq q hb rfl
  -- 3. pE1: erase bank.take keepBits
  have hndMask : (G0 :: c.src.take keepBits ++ c.bank.take keepBits).Nodup :=
    list_nodup_of_count_le hSrcDis (fun q => by
      have a := (List.take_sublist keepBits c.src).count_le q
      have b := (List.take_sublist keepBits c.bank).count_le q
      simp only [List.count_cons, List.count_append]; omega)
  have stE1 := eraseMask_correct G0 (c.src.take keepBits) (c.bank.take keepBits)
    (by simp [hsrcLen, hbankLen]) hndMask sM mE1 (by
      have e1 : regValue (c.bank.take keepBits) sM.basis = regValue (c.bank.take keepBits) sA.basis :=
        regValue_congr _ _ _ (fun q hq => sM_out q (fun h => hDstDisBank _ h (List.mem_of_mem_take hq))
          (fun h => hLiveDisBank _ h (List.mem_of_mem_take hq)))
      have e2 : sM.basis G0 = s.basis G0 := (sM_out _ hG0Out.2.1 hG0Out.2.2.1).trans (sA_out _ hG0Out.1)
      have e3 : regValue (c.src.take keepBits) sM.basis = regValue (c.src.take keepBits) s.basis :=
        regValue_congr _ _ _ (fun q hq => (sM_out q (fun h => hDstDisSrc _ h (List.mem_of_mem_take hq))
          (fun h => hLiveDisSrc _ h (List.mem_of_mem_take hq))).trans (sA_out q (hSrcDisBank _ (List.mem_of_mem_take hq))))
      rw [e1, e2, e3]; exact hTakeA)
  generalize hsE1 : run pE1 mE1 sM = sE1 at stE1 ⊢
  have sE1_park0 : ∀ h ∈ parkHosts, sE1.basis h = false := fun h hh =>
    (stE1.2.1 h (fun hb => hParkDisBank h hh (List.mem_of_mem_take hb))).trans (hZeros.1 h hh)
  -- 4. pD: dummies on zero parkHosts (no-op on state!)
  have stD : run pD mD sE1 = sE1 := ParkCopy.dummies_run parkHosts sE1 mD sE1_park0
  rw [stD]
  -- 5. pMI: move bank.drop keepBits into parkHosts
  have hDropLen : (c.bank.drop keepBits).length = parkHosts.length := by simp [hbankLen]; omega
  have hBankNd : c.bank.Nodup := (List.nodup_append.mp hndSB).2.1
  have hndMP : (c.bank.drop keepBits ++ parkHosts).Nodup :=
    List.nodup_append.mpr ⟨hBankNd.sublist (List.drop_sublist _ _), hParkNd,
      fun q hq r hr heq => hParkDisBank r hr (heq ▸ List.mem_of_mem_drop hq)⟩
  have stMI := ParkCopy.move_correct (c.bank.drop keepBits) parkHosts hDropLen hndMP sE1 mMI
    ((regValue_zero _ _).mpr sE1_park0)
  generalize hsMI : run pMI mMI sE1 = sMI at stMI ⊢
  -- Helper: track sMI vs s outside dst ∪ liveT ∪ parkHosts
  have hBankZero_MI : regValue c.bank sMI.basis = 0 := by
    rw [← List.take_append_drop keepBits c.bank, regValue_append]
    have h1 : regValue (c.bank.take keepBits) sMI.basis = 0 := by
      rw [regValue_congr _ _ sE1.basis (fun q hq => by
        have hnD : q ∉ c.bank.drop keepBits := by
          have := hBankNd; rw [← List.take_append_drop keepBits c.bank] at this
          exact fun hd => (List.nodup_append.mp this).2.2 q hq q hd rfl
        exact stMI.2.1 q hnD (fun hp => hParkDisBank q hp (List.mem_of_mem_take hq)))]
      exact stE1.2.2
    rw [h1, stMI.2.2.2]; simp
  have sMI_eq_s (q : Wire) (hd : q ∉ c.dst) (hl : q ∉ c.liveT) (hp : q ∉ parkHosts) :
      sMI.basis q = s.basis q := by
    by_cases hb : q ∈ c.bank
    · exact ((regValue_zero _ _).mp hBankZero_MI q hb).trans ((regValue_zero _ _).mp hBank0_s q hb).symm
    · have h1 := stMI.2.1 q (fun h => hb (List.mem_of_mem_drop h)) hp
      have h2 := stE1.2.1 q (fun h => hb (List.mem_of_mem_take h))
      exact h1.trans (h2.trans ((sM_out q hd hl).trans (sA_out q hb)))
  have sMI_eq_sM_dst (q : Wire) (hd : q ∈ c.dst) : sMI.basis q = sM.basis q := by
    have hnb : q ∉ c.bank := fun hb => hDstDisBank q hd hb
    have hnp : q ∉ parkHosts := fun hp => hParkDisDst q hp hd
    exact (stMI.2.1 q (fun h => hnb (List.mem_of_mem_drop h)) hnp).trans
      (stE1.2.1 q (fun h => hnb (List.mem_of_mem_take h)))
  -- 6. pB: renameProgram foldPerm (bodySwap body) = body on sMI
  have sMI_4834 : sMI.basis 4834 = false :=
    (sMI_eq_s 4834 (fun h => h4834_notReal (by simp [SplitCfg.realAll, h]))
      (fun h => h4834_notReal (by clear * - h; simp only [SplitCfg.realAll, SplitCfg.liveT, List.mem_cons, List.mem_append] at h ⊢; tauto))
      (fun h => (hParkDisSw _ h).1 rfl)).trans h4834_0
  have sMI_4875 : sMI.basis 4875 = false :=
    (sMI_eq_s 4875 (fun h => h4875_notReal (by simp [SplitCfg.realAll, h]))
      (fun h => h4875_notReal (by clear * - h; simp only [SplitCfg.realAll, SplitCfg.liveT, List.mem_cons, List.mem_append] at h ⊢; tauto))
      (fun h => (hParkDisSw _ h).2.2.1 rfl)).trans h4875_0
  have sMI_5093 : sMI.basis 5093 = false :=
    ((stMI.2.1 5093 (fun h => h5093_notBank (List.mem_of_mem_drop h)) (fun h => (hParkDisSw _ h).2.1 rfl)).trans
      (stE1.2.1 5093 (fun h => h5093_notBank (List.mem_of_mem_take h)))).trans hZeros.2.1
  have sMI_5478 : sMI.basis 5478 = false :=
    ((stMI.2.1 5478 (fun h => h5478_notBank (List.mem_of_mem_drop h)) (fun h => (hParkDisSw _ h).2.2.2 rfl)).trans
      (stE1.2.1 5478 (fun h => h5478_notBank (List.mem_of_mem_take h)))).trans hZeros.2.2
  -- Build clean reference state t for callback
  let t : State := { phase := sMI.phase, basis := fun q => if q ∈ c.dst then sM.basis q else s.basis q }
  have t_dst : regValue c.dst t.basis = P ^ 2 := by
    rw [regValue_congr c.dst t.basis sM.basis (fun q hq => by simp [t, hq]), sM_dst]
  have cb := callback t mB t_dst (fun q hq => by simp [t, hq])
  have body_dis_live : ∀ q ∈ wires body, q ∉ c.liveT := fun q hq hl =>
    (hLiveSub q hl).elim (fun h => hBodyDisE0 q h hq) (fun h => hBodyDisWorkT q h hq)
  have body_dis_park : ∀ q ∈ wires body, q ∉ parkHosts := fun q hq hp =>
    (hParkIn q hp).elim (fun h => hBodyDisE0 q h hq) (fun h => hBodyDisEU (h ▸ hp) (h ▸ hq))
  have locB := ECDSAAdd.run_measured_locality body (wires body) (Finset.Subset.refl _) sMI t mB rfl
    (fun q hq => by
      by_cases hd : q ∈ c.dst
      · simp [t, hd]; exact sMI_eq_sM_dst q hd
      · simp [t, hd]; exact sMI_eq_s q hd (body_dis_live q hq) (body_dis_park q hq))
  have runBody_phase : (run body mB sMI).phase = sMI.phase := locB.1.trans cb.1
  have runBody_out : regValue K0.core.out (run body mB sMI).basis = V := by
    rw [regValue_congr K0.core.out (run body mB sMI).basis (run body mB t).basis (fun q hq => by
      by_cases hw : q ∈ wires body
      · exact locB.2 q hw
      · rw [run_preserves_outside body mB sMI q hw, run_preserves_outside body mB t q hw]
        have hnd : q ∉ c.dst := fun h => hDstDisOut q h hq
        simp only [t, hnd, if_false]
        exact sMI_eq_s q hnd (fun h => hLiveDisOut q h hq) (fun h => hParkDisOut q h hq))]
    exact cb.2.1
  have runBody_keep (q : Wire) (ho : q ∉ K0.core.out) : (run body mB sMI).basis q = sMI.basis q := by
    by_cases hw : q ∈ wires body
    · rw [locB.2 q hw, cb.2.2 q ho]
      by_cases hd : q ∈ c.dst
      · simp [t, hd]; exact (sMI_eq_sM_dst q hd).symm
      · simp [t, hd]; exact (sMI_eq_s q hd (body_dis_live q hw) (body_dis_park q hw)).symm
    · exact run_preserves_outside body mB sMI q hw
  have hFoldPerm : LowZero18Square.foldPerm K0 E0 = Equiv.swap 4834 5093 := by
    ext x; rw [StairSquareSites.LT48K.foldPerm_eq, Equiv.swap_apply_def]; rfl
  have hSqSwap : R2SqEp760.sqSwap K0 E0 = Equiv.swap 4875 5478 := by
    ext x; rw [StairSquareSites.LT48K.sqSwap_eq, Equiv.swap_apply_def]; rfl
  have eqSq : run (R2SqEp760.bodySwap K0 E0 body) mB sMI = run body mB sMI := by
    rw [R2SqEp760.bodySwap, hSqSwap]
    exact swap_run_eq 4875 5478 body sMI mB (sMI_4875.trans sMI_5478.symm)
      ((runBody_keep 4875 hSwMem.2.2.2.2.1).trans (sMI_4875.trans (sMI_5478.symm.trans (runBody_keep 5478 hSwMem.2.2.2.2.2.1).symm)))
  have eqPB : run pB mB sMI = run body mB sMI := by
    change run (renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)) mB sMI = _
    rw [hFoldPerm]
    refine (swap_run_eq 4834 5093 (R2SqEp760.bodySwap K0 E0 body) sMI mB
      (sMI_4834.trans sMI_5093.symm) ?_).trans eqSq
    rw [eqSq, runBody_keep 4834 hSwMem.2.2.1, runBody_keep 5093 hSwMem.2.2.2.1, sMI_4834, sMI_5093]
  generalize hsB : run pB mB sMI = sB at eqPB ⊢
  have sB_phase : sB.phase = sMI.phase := by rw [eqPB]; exact runBody_phase
  have sB_out : regValue K0.core.out sB.basis = V := by rw [eqPB]; exact runBody_out
  have sB_keep (q : Wire) (ho : q ∉ K0.core.out) : sB.basis q = sMI.basis q := by rw [eqPB]; exact runBody_keep q ho
  -- 7. pC1: CachedSquareCopy restores bank.take keepBits
  have sB_dst : regValue c.dst sB.basis = P ^ 2 := by
    rw [regValue_congr c.dst sB.basis sM.basis (fun q hq => (sB_keep q (hDstDisOut q hq)).trans (sMI_eq_sM_dst q hq)), sM_dst]
  have sB_G0 : sB.basis G0 = s.basis G0 :=
    (sB_keep G0 hG0Out.2.2.2.2).trans (sMI_eq_s G0 hG0Out.2.1 hG0Out.2.2.1 hParkDisG0)
  have sB_src : regValue c.src sB.basis = regValue c.src s.basis :=
    regValue_congr c.src sB.basis s.basis (fun q hq =>
      (sB_keep q (hSrcDisOut q hq)).trans
      (sMI_eq_s q (fun h => hDstDisSrc _ h hq) (fun h => hLiveDisSrc _ h hq) (fun h => hParkDisSrc _ h hq)))
  have hCached : sB.basis (LowZero18Square.cacheWire K0 c.dst) =
      (sB.basis G0 && sB.basis ((c.src.take keepBits).headD 0)) := by
    rw [hCacheEq, ParkCopy.headD_take c.src keepBits hkPos]
    have hsq := CachedSquareCopy.square_head c.src c.dst G0 sB (by omega) (by rw [v.dstLen]; omega)
      (by rw [sB_dst, sB_G0, sB_src])
    exact hsq
  have eqC1 : run pC1 mC1 sB = run (copyRegister (some G0) (c.src.take keepBits) (c.bank.take keepBits)) mC1 sB :=
    CachedSquareCopy.run_eq G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits) sB mC1 hCached
  have hndSB_k : (c.src.take keepBits ++ c.bank.take keepBits).Nodup := (List.nodup_cons.mp hndMask).2
  have hG0B_k : ∀ x ∈ some G0, x ∉ c.bank.take keepBits := fun x hx hb => hG0B x hx (List.mem_of_mem_take hb)
  have stC1 := copyRegister_correct (some G0) (c.src.take keepBits) (c.bank.take keepBits)
    (by simp [hsrcLen, hbankLen]) hndSB_k hG0B_k sB mC1
  rw [← eqC1] at stC1
  generalize hsC1 : run pC1 mC1 sB = sC1 at stC1 ⊢
  have sB_bk0 : regValue (c.bank.take keepBits) sB.basis = 0 := by
    rw [regValue_congr _ _ sMI.basis (fun q hq => sB_keep q (hBankDisOut q (List.mem_of_mem_take hq)))]
    exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hBankZero_MI q (List.mem_of_mem_take hq))
  have sC1_bk : regValue (c.bank.take keepBits) sC1.basis = regValue (c.bank.take keepBits) sA.basis := by
    have h := stC1.2.2
    rw [sB_bk0, Nat.zero_xor] at h
    have hsrc_k : regValue (c.src.take keepBits) sB.basis = regValue (c.src.take keepBits) s.basis :=
      regValue_congr _ _ s.basis (fun q hq =>
        (sB_keep q (hSrcDisOut q (List.mem_of_mem_take hq))).trans
        (sMI_eq_s q (fun h' => hDstDisSrc _ h' (List.mem_of_mem_take hq))
          (fun h' => hLiveDisSrc _ h' (List.mem_of_mem_take hq))
          (fun h' => hParkDisSrc _ h' (List.mem_of_mem_take hq))))
    rw [h]; simp only [copyValue, sB_G0, hsrc_k]; exact hTakeA.symm
  -- 8. pMO: move parkHosts back into bank.drop keepBits
  have hndPM : (parkHosts ++ c.bank.drop keepBits).Nodup := (List.perm_append_comm.nodup_iff).mp hndMP
  have hDropNotTake : ∀ q ∈ c.bank.drop keepBits, q ∉ c.bank.take keepBits := by
    intro q hd ht
    have := hBankNd; rw [← List.take_append_drop keepBits c.bank] at this
    exact (List.nodup_append.mp this).2.2 q ht q hd rfl
  have sC1_drop0 : regValue (c.bank.drop keepBits) sC1.basis = 0 :=
    (regValue_congr _ _ sMI.basis (fun q hq =>
      (stC1.2.1 q (hDropNotTake q hq)).trans (sB_keep q (hBankDisOut q (List.mem_of_mem_drop hq))))).trans stMI.2.2.2
  have stMO := ParkCopy.move_correct parkHosts (c.bank.drop keepBits) hDropLen.symm hndPM sC1 mMO sC1_drop0
  generalize hsMO : run pMO mMO sC1 = sMO at stMO ⊢
  -- Key state invariants on sMO before c.clear!
  have sMO_eq_sM_of_not_out (q : Wire) (ho : q ∉ K0.core.out) (hb : q ∉ c.bank) : sMO.basis q = sM.basis q := by
    by_cases hp : q ∈ parkHosts
    · have h0_mo : sMO.basis q = false := (regValue_zero _ _).mp stMO.2.2.2 q hp
      have h0_m : sM.basis q = false := hZeros.1 q hp
      exact h0_mo.trans h0_m.symm
    · have h1 := stMO.2.1 q hp (fun h => hb (List.mem_of_mem_drop h))
      have h2 := stC1.2.1 q (fun h => hb (List.mem_of_mem_take h))
      have h3 := sB_keep q ho
      have h4 := stMI.2.1 q (fun h => hb (List.mem_of_mem_drop h)) hp
      have h5 := stE1.2.1 q (fun h => hb (List.mem_of_mem_take h))
      exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have sMO_bank : regValue c.bank sMO.basis = P := by
    rw [← List.take_append_drop keepBits c.bank, regValue_append]
    have h1 : regValue (c.bank.take keepBits) sMO.basis = regValue (c.bank.take keepBits) sA.basis := by
      rw [regValue_congr _ _ sC1.basis (fun q hq =>
        stMO.2.1 q (fun hp => hParkDisBank q hp (List.mem_of_mem_take hq)) (fun hd => hDropNotTake q hd hq)), sC1_bk]
    have h2 : regValue (c.bank.drop keepBits) sMO.basis = regValue (c.bank.drop keepBits) sA.basis := by
      rw [stMO.2.2.1]
      rw [regValue_congr parkHosts sC1.basis sMI.basis (fun q hq =>
        (stC1.2.1 q (fun ht => hParkDisBank q hq (List.mem_of_mem_take ht))).trans (sB_keep q (hParkDisOut q hq)))]
      rw [stMI.2.2.1]
      exact regValue_congr _ _ sA.basis (fun q hq =>
        (stE1.2.1 q (hDropNotTake q hq)).trans
          (sM_out q (fun h => hDstDisBank _ h (List.mem_of_mem_drop hq))
            (fun h => hLiveDisBank _ h (List.mem_of_mem_drop hq))))
    rw [h1, h2, ← regValue_append, List.take_append_drop, sA_bank]
  have sMO_bank_bit (q : Wire) (hq : q ∈ c.bank) : sMO.basis q = sA.basis q := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    have b1 := RawClearCarryProbe.register_bit c.bank i sMO.basis hi
    have b2 := RawClearCarryProbe.register_bit c.bank i sA.basis hi
    have hg : c.bank.getD i 0 = c.bank[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hg] at b1 b2; rw [b1, b2, sMO_bank, sA_bank]
  have sMO_lo : regValue c.R.lo sMO.basis = regValue c.R.lo sA.basis :=
    regValue_congr _ _ _ (fun q hq => sMO_bank_bit q (List.mem_of_mem_take hq))
  have sMO_hi : regValue c.R.hi sMO.basis = regValue c.R.hi sA.basis :=
    regValue_congr _ _ _ (fun q hq => sMO_bank_bit q (List.mem_of_mem_drop hq))
  have sMO_dst : regValue c.dst sMO.basis = (regValue c.bank sMO.basis) ^ 2 := by
    rw [regValue_congr c.dst sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q (hDstDisOut q hq) (hDstDisBank q hq)),
      sM_dst, sMO_bank]
  have sMO_T : regValue c.T sMO.basis = 2 * regValue c.R.lo sMO.basis * regValue c.R.hi sMO.basis := by
    rw [regValue_congr c.T sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.1, sMO_lo, sMO_hi]
  have sMO_T1 : regValue c.T1 sMO.basis = 2 * (regValue c.R.lo sMO.basis % 2 ^ 32) * (regValue c.R.lo sMO.basis / 2 ^ 32) := by
    rw [regValue_congr c.T1 sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.2.1, sMO_lo]
  have sMO_T2 : regValue c.T2 sMO.basis = 2 * (regValue c.R.hi sMO.basis % 2 ^ c.Q2.h) * (regValue c.R.hi sMO.basis / 2 ^ c.Q2.h) := by
    rw [regValue_congr c.T2 sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.2.2.1, sMO_hi]
  have sMO_T5 : regValue c.T5 sMO.basis = 2 * ((regValue c.R.lo sMO.basis + regValue c.R.hi sMO.basis) % 2 ^ 33) *
      ((regValue c.R.lo sMO.basis + regValue c.R.hi sMO.basis) / 2 ^ 33) := by
    rw [regValue_congr c.T5 sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.2.2.2.1, sMO_lo, sMO_hi]
  have sMO_sc0 : regValue c.cleanScratch sMO.basis = 0 := by
    rw [regValue_congr c.cleanScratch sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q (hScDisOut q hq) (hScDisBank q hq))]
    refine (regValue_congr c.cleanScratch sM.basis sA.basis (fun q hq => sM_out q
      (kdis v.realNd (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.cleanScratch, List.count_cons, List.count_append, List.count_nil]; omega) q hq)
      (kdis v.realNd (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.cleanScratch, SplitCfg.liveT, List.count_cons, List.count_append, List.count_nil]; omega) q hq))).trans sA_sc0
  have sMO_cin0 : sMO.basis K0.core.cin = false :=
    (sMO_eq_sM_of_not_out K0.core.cin hCin_notOut hCin_notBank).trans
      ((sM_out K0.core.cin hCin_notDst hCin_notLive).trans sA_cin0)
  -- 9. pCL: c.clear uncomputes dst and liveT to 0
  have stCL := cfg_clear_correct c v sMO mCL sMO_dst sMO_T sMO_T1 sMO_T2 sMO_T5 sMO_sc0 sMO_cin0
  generalize hsCL : run pCL mCL sMO = sCL at stCL ⊢
  -- 10. pE: eraseMask erases bank back to 0
  have stE := eraseMask_correct G0 c.src c.bank hsrc_bank hSrcDis sCL mE (by
    have e1 : regValue c.bank sCL.basis = P :=
      (regValue_congr c.bank sCL.basis sMO.basis (fun q hq =>
        stCL.2.2.2 q (fun h => hDstDisBank _ h hq) (fun h => hLiveDisBank _ h hq))).trans sMO_bank
    have e2 : sCL.basis G0 = s.basis G0 :=
      (stCL.2.2.2 G0 hG0Out.2.1 hG0Out.2.2.1).trans
        ((sMO_eq_sM_of_not_out G0 hG0Out.2.2.2.2 hG0Out.1).trans
          ((sM_out G0 hG0Out.2.1 hG0Out.2.2.1).trans (sA_out G0 hG0Out.1)))
    have e3 : regValue c.src sCL.basis = regValue c.src s.basis :=
      regValue_congr c.src sCL.basis s.basis (fun q hq =>
        (stCL.2.2.2 q (fun h => hDstDisSrc _ h hq) (fun h => hLiveDisSrc _ h hq)).trans
          ((sMO_eq_sM_of_not_out q (hSrcDisOut q hq) (hSrcDisBank q hq)).trans
            ((sM_out q (fun h => hDstDisSrc _ h hq) (fun h => hLiveDisSrc _ h hq)).trans
              (sA_out q (hSrcDisBank q hq)))))
    rw [e1, e2, e3])
  generalize hsE : run pE mE sCL = sE at stE ⊢
  refine ⟨?_, ?_, ?_⟩
  · exact stE.1.trans (stCL.1.trans (stMO.1.trans (stC1.1.trans (sB_phase.trans
      (stMI.1.trans (stE1.1.trans (stM.1.trans stA.1)))))))
  · rw [regValue_congr K0.core.out sE.basis sB.basis (fun q hq =>
      (stE.2.1 q (fun h => hBankDisOut q h hq)).trans
      ((stCL.2.2.2 q (fun h => hDstDisOut q h hq) (fun h => hLiveDisOut q h hq)).trans
      ((stMO.2.1 q (fun h => hParkDisOut q h hq) (fun h => hBankDisOut q (List.mem_of_mem_drop h) hq)).trans
       (stC1.2.1 q (fun h => hBankDisOut q (List.mem_of_mem_take h) hq)))))]
    exact sB_out
  · intro q ho
    by_cases hb : q ∈ c.bank
    · exact ((regValue_zero _ _).mp stE.2.2 q hb).trans ((regValue_zero _ _).mp hBank0_s q hb).symm
    · rw [stE.2.1 q hb]
      by_cases hd : q ∈ c.dst
      · exact ((regValue_zero _ _).mp stCL.2.1 q hd).trans ((regValue_zero _ _).mp hd0 q hd).symm
      · by_cases hl : q ∈ c.liveT
        · exact ((regValue_zero _ _).mp stCL.2.2.1 q hl).trans ((regValue_zero _ _).mp hLive0_s q hl).symm
        · exact (stCL.2.2.2 q hd hl).trans ((sMO_eq_sM_of_not_out q ho hb).trans ((sM_out q hd hl).trans (sA_out q hb)))

/-! ### Zero-bit proofs for parked hosts and swap hosts after `make` -/

private theorem getD_take {α : Type} (l : List α) (n i : Nat) (d : α) (hi : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

private theorem getD_drop {α : Type} (l : List α) (k i : Nat) (d : α) :
    (l.drop k).getD i d = l.getD (k + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem cfg128_zeros (c : SplitCfg) (v : CfgValid c) (hn : c.n = 128)
    (hT5_0 : c.T5.getD 0 0 = E0.getD 231 0)
    (hT5_66 : c.T5.getD 66 0 = E0.getD 298 0)
    (hT5_67 : c.T5.getD 67 0 = E0.getD 299 0)
    (hT_eq : c.T = E0.take 130) (hT1_eq : c.T1 = (E0.drop 132).take 66) (hT2_eq : c.T2 = (E0.drop 232).take 66)
    (parkHosts : List Wire)
    (hParkSub : ∀ h ∈ parkHosts, h ∈ ParkCopy.hosts E0 ∨ h = ControlLoan1589BFFold.eU K0)
    (h130_not : E0.getD 130 0 ∉ c.dst ∧ E0.getD 130 0 ∉ c.liveT)
    (h131_not : E0.getD 131 0 ∉ c.dst ∧ E0.getD 131 0 ∉ c.liveT)
    (heU_not : ControlLoan1589BFFold.eU K0 ∉ c.dst ∧ ControlLoan1589BFFold.eU K0 ∉ c.liveT)
    (s0 : State) (m0 : List Bool)
    (hd0 : regValue c.dst s0.basis = 0) (hT0 : regValue c.liveT s0.basis = 0)
    (hSc0 : regValue c.cleanScratch s0.basis = 0) (hi0 : s0.basis K0.core.cin = false)
    (heu0 : ControlLoan1589BFFold.eU K0 ∈ parkHosts → s0.basis (ControlLoan1589BFFold.eU K0) = false)
    (he0 : ∀ q ∈ E0, s0.basis q = false) :
    (∀ h ∈ parkHosts, (run c.make m0 s0).basis h = false) ∧
    (run c.make m0 s0).basis 5093 = false ∧ (run c.make m0 s0).basis 5478 = false := by
  have st := cfg_make_correct c v s0 m0 hd0 hT0 hSc0 hi0
  set u := run c.make m0 s0
  set a := regValue c.R.lo s0.basis
  set b := regValue c.R.hi s0.basis
  have haLt : a < 2 ^ 64 := by
    have : c.R.lo.length = 64 := by simp [KRegs.lo, SplitCfg.R, v.bankLen, hn]
    simpa [this] using regValue_lt c.R.lo s0.basis
  have hbLt : b < 2 ^ 64 := by
    have : c.R.hi.length = 64 := by simp [KRegs.hi, SplitCfg.R, v.bankLen, hn]
    simpa [this] using regValue_lt c.R.hi s0.basis
  have hQ2h : c.Q2.h = 32 := by simp [SplitCfg.Q2, hn]
  have hElen : E0.length = 300 := by rw [E0_eq]; decide +kernel
  have h5093 : E0.getD 0 0 = 5093 := by rw [E0_eq]; decide +kernel
  have h5478 : E0.getD 130 0 = 5478 := by rw [E0_eq]; decide +kernel
  have bT0 : u.basis (E0.getD 0 0) = false := by
    have e : c.T.getD 0 0 = E0.getD 0 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact even_bit0_false c.T u.basis (a * b) (by rw [v.tLen, hn]; decide) (by rw [st.2.2.1]; ring)
  have bT129 : u.basis (E0.getD 129 0) = false := by
    have e : c.T.getD 129 0 = E0.getD 129 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; refine hi_bit_false c.T u.basis 129 (by rw [v.tLen, hn]; decide) ?_
    rw [st.2.2.1, Nat.mul_assoc]; have : a * b < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' haLt hbLt; omega
  have bT130 : u.basis (E0.getD 130 0) = false :=
    (st.2.2.2.2.2.2 _ h130_not.1 h130_not.2).trans (he0 _ (DiagSq.getD_in E0 130 (by omega)))
  have bT131 : u.basis (E0.getD 131 0) = false :=
    (st.2.2.2.2.2.2 _ h131_not.1 h131_not.2).trans (he0 _ (DiagSq.getD_in E0 131 (by omega)))
  have bT1_0 : u.basis (E0.getD 132 0) = false := by
    have e : c.T1.getD 0 0 = E0.getD 132 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false c.T1 u.basis ((a % 2 ^ 32) * (a / 2 ^ 32)) (by rw [v.t1Len]; decide) (by rw [st.2.2.2.1]; ring)
  have bT1_65 : u.basis (E0.getD 197 0) = false := by
    have e : c.T1.getD 65 0 = E0.getD 197 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false c.T1 u.basis 65 (by rw [v.t1Len]; decide) ?_
    rw [st.2.2.2.1, Nat.mul_assoc]
    have h1 : a % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : a / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (a % 2 ^ 32) * (a / 2 ^ 32) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT2_0 : u.basis (E0.getD 232 0) = false := by
    have e : c.T2.getD 0 0 = E0.getD 232 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false c.T2 u.basis ((b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h))
      (by have := v.t2Len; simp [hn] at this; omega) (by rw [st.2.2.2.2.1]; ring)
  have bT2_65 : u.basis (E0.getD 297 0) = false := by
    have e : c.T2.getD 65 0 = E0.getD 297 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false c.T2 u.basis 65 (by have := v.t2Len; simp [hn] at this; omega) ?_
    rw [st.2.2.2.2.1, hQ2h, Nat.mul_assoc]
    have h1 : b % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : b / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (b % 2 ^ 32) * (b / 2 ^ 32) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT5_0 : u.basis (E0.getD 231 0) = false := by
    rw [← hT5_0]; exact even_bit0_false c.T5 u.basis (((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33))
      (by rw [v.t5Len]; decide) (by rw [st.2.2.2.2.2.1]; ring)
  have bT5_lt : regValue c.T5 u.basis < 2 ^ 66 := by
    rw [st.2.2.2.2.2.1, Nat.mul_assoc]
    have h1 : (a + b) % 2 ^ 33 < 2 ^ 33 := Nat.mod_lt _ (by decide)
    have h2 : (a + b) / 2 ^ 33 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) < 2 ^ 33 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT5_66 : u.basis (E0.getD 298 0) = false := by
    rw [← hT5_66]; exact hi_bit_false c.T5 u.basis 66 (by rw [v.t5Len]; decide) bT5_lt
  have bT5_67 : u.basis (E0.getD 299 0) = false := by
    rw [← hT5_67]; exact hi_bit_false c.T5 u.basis 67 (by rw [v.t5Len]; decide) (by omega)
  refine ⟨?_, by rwa [← h5093], by rwa [← h5478]⟩
  intro h hh
  rcases hParkSub h hh with hp | rfl
  · simp only [ParkCopy.hosts, ParkCopy.hostIdx, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [bT129, bT131, bT1_0, bT1_65, bT5_0, bT2_0, bT2_65, bT5_66, bT5_67]
  · exact (st.2.2.2.2.2.2 _ heU_not.1 heU_not.2).trans (heu0 hh)

private theorem cfgC_zeros (s0 : State) (m0 : List Bool)
    (hd0 : regValue cfgC.dst s0.basis = 0) (hT0 : regValue cfgC.liveT s0.basis = 0)
    (hSc0 : regValue cfgC.cleanScratch s0.basis = 0) (hi0 : s0.basis K0.core.cin = false)
    (_ : ControlLoan1589BFFold.eU K0 ∈ ParkCopyS.hostsS E0 → s0.basis (ControlLoan1589BFFold.eU K0) = false)
    (_ : ∀ q ∈ E0, s0.basis q = false) :
    (∀ h ∈ ParkCopyS.hostsS E0, (run cfgC.make m0 s0).basis h = false) ∧
    (run cfgC.make m0 s0).basis 5093 = false ∧ (run cfgC.make m0 s0).basis 5478 = false := by
  have st := cfg_make_correct cfgC cfgC_valid s0 m0 hd0 hT0 hSc0 hi0
  set u := run cfgC.make m0 s0
  set a := regValue cfgC.R.lo s0.basis
  set b := regValue cfgC.R.hi s0.basis
  have hbl : cfgC.bank.length = 129 := cfgC_valid.bankLen
  have ht2 : cfgC.T2.length = 68 := cfgC_valid.t2Len
  have haLt : a < 2 ^ 64 := by
    have : cfgC.R.lo.length = 64 := by simp only [KRegs.lo, SplitCfg.R, List.length_take, hbl]; decide
    simpa [this] using regValue_lt cfgC.R.lo s0.basis
  have hbLt : b < 2 ^ 65 := by
    have : cfgC.R.hi.length = 65 := by simp only [KRegs.hi, SplitCfg.R, List.length_drop, hbl]
    simpa [this] using regValue_lt cfgC.R.hi s0.basis
  have hQ2h : cfgC.Q2.h = 33 := by simp [SplitCfg.Q2, cfgC]
  have hT_eq : cfgC.T = E0.take 132 := by simp [SplitCfg.T, cfgC]
  have hT1_eq : cfgC.T1 = (E0.drop 132).take 66 := rfl
  have hT2_eq : cfgC.T2 = (E0.drop 232).take 68 := rfl
  have h5093 : E0.getD 0 0 = 5093 := by rw [E0_eq]; decide +kernel
  have h5478 : E0.getD 130 0 = 5478 := by rw [E0_eq]; decide +kernel
  have bT0 : u.basis (E0.getD 0 0) = false := by
    have e : cfgC.T.getD 0 0 = E0.getD 0 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact even_bit0_false cfgC.T u.basis (a * b) (by rw [cfgC_valid.tLen]; decide) (by rw [st.2.2.1]; ring)
  have hT_lt : regValue cfgC.T u.basis < 2 ^ 130 := by
    rw [st.2.2.1, Nat.mul_assoc]; have : a * b < 2 ^ 64 * 2 ^ 65 := Nat.mul_lt_mul'' haLt hbLt; omega
  have bT130 : u.basis (E0.getD 130 0) = false := by
    have e : cfgC.T.getD 130 0 = E0.getD 130 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact hi_bit_false cfgC.T u.basis 130 (by rw [cfgC_valid.tLen]; decide) hT_lt
  have bT131 : u.basis (E0.getD 131 0) = false := by
    have e : cfgC.T.getD 131 0 = E0.getD 131 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact hi_bit_false cfgC.T u.basis 131 (by rw [cfgC_valid.tLen]; decide) (by omega)
  have bT1_0 : u.basis (E0.getD 132 0) = false := by
    have e : cfgC.T1.getD 0 0 = E0.getD 132 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false cfgC.T1 u.basis ((a % 2 ^ 32) * (a / 2 ^ 32)) (by rw [cfgC_valid.t1Len]; decide) (by rw [st.2.2.2.1]; ring)
  have bT1_65 : u.basis (E0.getD 197 0) = false := by
    have e : cfgC.T1.getD 65 0 = E0.getD 197 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false cfgC.T1 u.basis 65 (by rw [cfgC_valid.t1Len]; decide) ?_
    rw [st.2.2.2.1, Nat.mul_assoc]
    have h1 : a % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : a / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (a % 2 ^ 32) * (a / 2 ^ 32) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT2_0 : u.basis (E0.getD 232 0) = false := by
    have e : cfgC.T2.getD 0 0 = E0.getD 232 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false cfgC.T2 u.basis ((b % 2 ^ cfgC.Q2.h) * (b / 2 ^ cfgC.Q2.h))
      (by omega) (by rw [st.2.2.2.2.1]; ring)
  have bT2_67 : u.basis (E0.getD 299 0) = false := by
    have e : cfgC.T2.getD 67 0 = E0.getD 299 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false cfgC.T2 u.basis 67 (by omega) ?_
    rw [st.2.2.2.2.1, hQ2h, Nat.mul_assoc]
    have h1 : b % 2 ^ 33 < 2 ^ 33 := Nat.mod_lt _ (by decide)
    have h2 : b / 2 ^ 33 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (b % 2 ^ 33) * (b / 2 ^ 33) < 2 ^ 33 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  refine ⟨?_, by rwa [← h5093], by rwa [← h5478]⟩
  intro h hh
  simp only [ParkCopyS.hostsS, ParkCopyS.hostIdxS, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl
  exacts [bT131, bT1_0, bT1_65, bT2_0, bT2_67]

/-! ### Branch equivalences (`brC`, `brB`, `brA`) and `coreOK` -/

private theorem mask_union_mem (A B C : List Nat)
    (h : A.all (fun q => (StairSquareBChecks.LT48B.maskL B).testBit q || (StairSquareBChecks.LT48B.maskL C).testBit q) = true) :
    ∀ q ∈ A, q ∈ B ∨ q ∈ C := by
  intro q hq
  have t := List.all_eq_true.mp h q hq
  simp only [Bool.or_eq_true, StairSquareBChecks.LT48B.testBit_maskL, decide_eq_true_eq] at t
  exact t

private theorem memory_cfgA_geom_hS : 118 + (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).length = cfgA.n ∧
    cfgA.src.length = cfgA.n ∧ (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).Nodup ∧
    (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0) ∧
    (G0 ∉ cfgA.bank ∧ G0 ∉ cfgA.dst ∧ G0 ∉ cfgA.liveT ∧ G0 ∉ cfgA.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgA.dst = cfgA.dst.headD 0 ∧
    (E0.getD 130 0 ∉ cfgA.dst ∧ E0.getD 130 0 ∉ cfgA.liveT ∧ E0.getD 131 0 ∉ cfgA.dst ∧ E0.getD 131 0 ∉ cfgA.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ cfgA.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgA.liveT) ∧
    (cfgA.T5.getD 0 0 = E0.getD 231 0 ∧ cfgA.T5.getD 66 0 = E0.getD 298 0 ∧ cfgA.T5.getD 67 0 = E0.getD 299 0) := by
  simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel

private theorem memory_cfgA_geom_hnd : (G0 :: cfgA.src ++ cfgA.bank).Nodup :=
  PeakNodup.nodup_of_mask _ (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hPB : ∀ q ∈ (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)), q ∉ cfgA.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hPS : ∀ q ∈ (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)), q ∉ cfgA.src :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hPD : ∀ q ∈ (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)), q ∉ cfgA.dst :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) cfgA.dst (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hPO : ∀ q ∈ (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)), q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hEB : ∀ q ∈ E0, q ∉ cfgA.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL E0 cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hWW : ∀ q ∈ cfgA.workT, q ∈ K0.core.work :=
  StairSquareBChecks.LT48B.sub_of_maskL cfgA.workT K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hLU : ∀ q ∈ cfgA.liveT, q ∈ E0 ∨ q ∈ cfgA.workT :=
  mask_union_mem cfgA.liveT E0 cfgA.workT (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hLB : ∀ q ∈ cfgA.liveT, q ∉ cfgA.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.liveT cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hLS : ∀ q ∈ cfgA.liveT, q ∉ cfgA.src :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.liveT cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hLO : ∀ q ∈ cfgA.liveT, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.liveT K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hSU : ∀ q ∈ cfgA.cleanScratch, q ∈ K0.foldPad ∨ q ∈ K0.core.work :=
  mask_union_mem cfgA.cleanScratch K0.foldPad K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hSB : ∀ q ∈ cfgA.cleanScratch, q ∉ cfgA.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hSS : ∀ q ∈ cfgA.cleanScratch, q ∉ cfgA.src :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hSO : ∀ q ∈ cfgA.cleanScratch, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hSP : ∀ q ∈ cfgA.cleanScratch, q ∉ (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hDB : ∀ q ∈ cfgA.dst, q ∉ cfgA.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.dst cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hDS : ∀ q ∈ cfgA.dst, q ∉ cfgA.src :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.dst cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hDO : ∀ q ∈ cfgA.dst, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.dst K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hBO : ∀ q ∈ cfgA.bank, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.bank K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgA_geom_hSrO : ∀ q ∈ cfgA.src, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgA.src K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem cfgA_geom :
    118 + (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).length = cfgA.n ∧
    cfgA.src.length = cfgA.n ∧
    (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).Nodup ∧
    (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∉ cfgA.bank ∧ h ∉ cfgA.src ∧ h ∉ cfgA.dst ∧
      h ∉ K0.core.out ∧ h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0) ∧
    (G0 :: cfgA.src ++ cfgA.bank).Nodup ∧
    (∀ q ∈ E0, q ∉ cfgA.bank) ∧
    (∀ q ∈ cfgA.workT, q ∈ K0.core.work) ∧
    (∀ q ∈ cfgA.liveT, (q ∈ E0 ∨ q ∈ cfgA.workT) ∧ q ∉ cfgA.bank ∧ q ∉ cfgA.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgA.cleanScratch, (q ∈ K0.foldPad ∨ q ∈ K0.core.work) ∧ q ∉ cfgA.bank ∧ q ∉ cfgA.src ∧
      q ∉ K0.core.out ∧ q ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) ∧
    (∀ q ∈ cfgA.dst, q ∉ cfgA.bank ∧ q ∉ cfgA.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgA.bank, q ∉ K0.core.out) ∧
    (∀ q ∈ cfgA.src, q ∉ K0.core.out) ∧
    (G0 ∉ cfgA.bank ∧ G0 ∉ cfgA.dst ∧ G0 ∉ cfgA.liveT ∧ G0 ∉ cfgA.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgA.dst = cfgA.dst.headD 0 ∧
    (E0.getD 130 0 ∉ cfgA.dst ∧ E0.getD 130 0 ∉ cfgA.liveT ∧ E0.getD 131 0 ∉ cfgA.dst ∧ E0.getD 131 0 ∉ cfgA.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ cfgA.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgA.liveT) ∧
    (cfgA.T5.getD 0 0 = E0.getD 231 0 ∧ cfgA.T5.getD 66 0 = E0.getD 298 0 ∧ cfgA.T5.getD 67 0 = E0.getD 299 0) := by
  have hS := memory_cfgA_geom_hS
  have hnd := memory_cfgA_geom_hnd
  have hPB := memory_cfgA_geom_hPB
  have hPS := memory_cfgA_geom_hPS
  have hPD := memory_cfgA_geom_hPD
  have hPO := memory_cfgA_geom_hPO
  have hEB := memory_cfgA_geom_hEB
  have hWW := memory_cfgA_geom_hWW
  have hLU := memory_cfgA_geom_hLU
  have hLB := memory_cfgA_geom_hLB
  have hLS := memory_cfgA_geom_hLS
  have hLO := memory_cfgA_geom_hLO
  have hSU := memory_cfgA_geom_hSU
  have hSB := memory_cfgA_geom_hSB
  have hSS := memory_cfgA_geom_hSS
  have hSO := memory_cfgA_geom_hSO
  have hSP := memory_cfgA_geom_hSP
  have hDB := memory_cfgA_geom_hDB
  have hDS := memory_cfgA_geom_hDS
  have hDO := memory_cfgA_geom_hDO
  have hBO := memory_cfgA_geom_hBO
  have hSrO := memory_cfgA_geom_hSrO
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1,
    fun h hh => ⟨hPB h hh, hPS h hh, hPD h hh, hPO h hh, hS.2.2.2.2.1 h hh⟩,
    hS.2.2.2.2.2.1, hnd, hEB, hWW,
    fun q hq => ⟨hLU q hq, hLB q hq, hLS q hq, hLO q hq⟩,
    fun q hq => ⟨hSU q hq, hSB q hq, hSS q hq, hSO q hq, hSP q hq⟩,
    fun q hq => ⟨hDB q hq, hDS q hq, hDO q hq⟩, hBO, hSrO,
    hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.2⟩

/-! Independent finite receipts bound replay reduction caches per geometry part. -/
private theorem memory_cfgB_geom_hS : 119 + (ParkCopy.hosts E0).length = cfgB.n ∧
    cfgB.src.length = cfgB.n ∧ (ParkCopy.hosts E0).Nodup ∧
    (∀ h ∈ ParkCopy.hosts E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopy.hosts E0, h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopy.hosts E0 ∧
    (G0 ∉ cfgB.bank ∧ G0 ∉ cfgB.dst ∧ G0 ∉ cfgB.liveT ∧ G0 ∉ cfgB.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgB.dst = cfgB.dst.headD 0 ∧
    (E0.getD 130 0 ∉ cfgB.dst ∧ E0.getD 130 0 ∉ cfgB.liveT ∧ E0.getD 131 0 ∉ cfgB.dst ∧ E0.getD 131 0 ∉ cfgB.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ cfgB.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgB.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ ParkCopy.hosts E0) ∧
    (cfgB.T5.getD 0 0 = E0.getD 231 0 ∧ cfgB.T5.getD 66 0 = E0.getD 298 0 ∧ cfgB.T5.getD 67 0 = E0.getD 299 0) := by
  simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel

private theorem memory_cfgB_geom_hnd : (G0 :: cfgB.src ++ cfgB.bank).Nodup :=
  PeakNodup.nodup_of_mask _ (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hPB : ∀ q ∈ (ParkCopy.hosts E0), q ∉ cfgB.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hPS : ∀ q ∈ (ParkCopy.hosts E0), q ∉ cfgB.src :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hPD : ∀ q ∈ (ParkCopy.hosts E0), q ∉ cfgB.dst :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) cfgB.dst (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hPO : ∀ q ∈ (ParkCopy.hosts E0), q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hEB : ∀ q ∈ E0, q ∉ cfgB.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL E0 cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hWW : ∀ q ∈ cfgB.workT, q ∈ K0.core.work ∨ q = D0 := by
  have h := mask_union_mem cfgB.workT K0.core.work [D0] (by simp only [cfgB_fast, workTB_lit, K0_eq, D0_eq]; decide +kernel)
  intro q hq; exact (h q hq).imp_right List.mem_singleton.mp

private theorem memory_cfgB_geom_hLU : ∀ q ∈ cfgB.liveT, q ∈ E0 ∨ q ∈ cfgB.workT :=
  mask_union_mem cfgB.liveT E0 cfgB.workT (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hLB : ∀ q ∈ cfgB.liveT, q ∉ cfgB.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.liveT cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hLS : ∀ q ∈ cfgB.liveT, q ∉ cfgB.src :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.liveT cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hLO : ∀ q ∈ cfgB.liveT, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.liveT K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hSU : ∀ q ∈ cfgB.cleanScratch, q ∈ K0.foldPad ∨ q ∈ K0.core.work :=
  mask_union_mem cfgB.cleanScratch K0.foldPad K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hSB : ∀ q ∈ cfgB.cleanScratch, q ∉ cfgB.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hSS : ∀ q ∈ cfgB.cleanScratch, q ∉ cfgB.src :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hSO : ∀ q ∈ cfgB.cleanScratch, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hSP : ∀ q ∈ cfgB.cleanScratch, q ∉ (ParkCopy.hosts E0) :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch (ParkCopy.hosts E0) (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hDB : ∀ q ∈ cfgB.dst, q ∉ cfgB.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.dst cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hDS : ∀ q ∈ cfgB.dst, q ∉ cfgB.src :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.dst cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hDO : ∀ q ∈ cfgB.dst, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.dst K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hBO : ∀ q ∈ cfgB.bank, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.bank K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgB_geom_hSrO : ∀ q ∈ cfgB.src, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgB.src K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem cfgB_geom :
    119 + (ParkCopy.hosts E0).length = cfgB.n ∧
    cfgB.src.length = cfgB.n ∧
    (ParkCopy.hosts E0).Nodup ∧
    (∀ h ∈ ParkCopy.hosts E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopy.hosts E0, h ∉ cfgB.bank ∧ h ∉ cfgB.src ∧ h ∉ cfgB.dst ∧
      h ∉ K0.core.out ∧ h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopy.hosts E0 ∧
    (G0 :: cfgB.src ++ cfgB.bank).Nodup ∧
    (∀ q ∈ E0, q ∉ cfgB.bank) ∧
    (∀ q ∈ cfgB.workT, q ∈ K0.core.work ∨ q = D0) ∧
    (∀ q ∈ cfgB.liveT, (q ∈ E0 ∨ q ∈ cfgB.workT) ∧ q ∉ cfgB.bank ∧ q ∉ cfgB.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgB.cleanScratch, (q ∈ K0.foldPad ∨ q ∈ K0.core.work) ∧ q ∉ cfgB.bank ∧ q ∉ cfgB.src ∧
      q ∉ K0.core.out ∧ q ∉ ParkCopy.hosts E0) ∧
    (∀ q ∈ cfgB.dst, q ∉ cfgB.bank ∧ q ∉ cfgB.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgB.bank, q ∉ K0.core.out) ∧
    (∀ q ∈ cfgB.src, q ∉ K0.core.out) ∧
    (G0 ∉ cfgB.bank ∧ G0 ∉ cfgB.dst ∧ G0 ∉ cfgB.liveT ∧ G0 ∉ cfgB.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgB.dst = cfgB.dst.headD 0 ∧
    (E0.getD 130 0 ∉ cfgB.dst ∧ E0.getD 130 0 ∉ cfgB.liveT ∧ E0.getD 131 0 ∉ cfgB.dst ∧ E0.getD 131 0 ∉ cfgB.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ cfgB.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgB.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ ParkCopy.hosts E0) ∧
    (cfgB.T5.getD 0 0 = E0.getD 231 0 ∧ cfgB.T5.getD 66 0 = E0.getD 298 0 ∧ cfgB.T5.getD 67 0 = E0.getD 299 0) := by
  have hS := memory_cfgB_geom_hS
  have hnd := memory_cfgB_geom_hnd
  have hPB := memory_cfgB_geom_hPB
  have hPS := memory_cfgB_geom_hPS
  have hPD := memory_cfgB_geom_hPD
  have hPO := memory_cfgB_geom_hPO
  have hEB := memory_cfgB_geom_hEB
  have hWW := memory_cfgB_geom_hWW
  have hLU := memory_cfgB_geom_hLU
  have hLB := memory_cfgB_geom_hLB
  have hLS := memory_cfgB_geom_hLS
  have hLO := memory_cfgB_geom_hLO
  have hSU := memory_cfgB_geom_hSU
  have hSB := memory_cfgB_geom_hSB
  have hSS := memory_cfgB_geom_hSS
  have hSO := memory_cfgB_geom_hSO
  have hSP := memory_cfgB_geom_hSP
  have hDB := memory_cfgB_geom_hDB
  have hDS := memory_cfgB_geom_hDS
  have hDO := memory_cfgB_geom_hDO
  have hBO := memory_cfgB_geom_hBO
  have hSrO := memory_cfgB_geom_hSrO
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1,
    fun h hh => ⟨hPB h hh, hPS h hh, hPD h hh, hPO h hh, hS.2.2.2.2.1 h hh⟩,
    hS.2.2.2.2.2.1, hnd, hEB, hWW,
    fun q hq => ⟨hLU q hq, hLB q hq, hLS q hq, hLO q hq⟩,
    fun q hq => ⟨hSU q hq, hSB q hq, hSS q hq, hSO q hq, hSP q hq⟩,
    fun q hq => ⟨hDB q hq, hDS q hq, hDO q hq⟩, hBO, hSrO,
    hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.2⟩

/-! Independent finite receipts bound replay reduction caches per geometry part. -/
private theorem memory_cfgC_geom_hS : 124 + (ParkCopyS.hostsS E0).length = cfgC.n ∧
    cfgC.src.length = cfgC.n ∧ (ParkCopyS.hostsS E0).Nodup ∧
    (∀ h ∈ ParkCopyS.hostsS E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopyS.hostsS E0, h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopyS.hostsS E0 ∧
    (G0 ∉ cfgC.bank ∧ G0 ∉ cfgC.dst ∧ G0 ∉ cfgC.liveT ∧ G0 ∉ cfgC.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgC.dst = cfgC.dst.headD 0 ∧
    ControlLoan1589BFFold.eU K0 ∉ ParkCopyS.hostsS E0 := by
  simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel

private theorem memory_cfgC_geom_hnd : (G0 :: cfgC.src ++ cfgC.bank).Nodup :=
  PeakNodup.nodup_of_mask _ (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hPB : ∀ q ∈ (ParkCopyS.hostsS E0), q ∉ cfgC.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hPS : ∀ q ∈ (ParkCopyS.hostsS E0), q ∉ cfgC.src :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hPD : ∀ q ∈ (ParkCopyS.hostsS E0), q ∉ cfgC.dst :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) cfgC.dst (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hPO : ∀ q ∈ (ParkCopyS.hostsS E0), q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hEB : ∀ q ∈ E0, q ∉ cfgC.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL E0 cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hWW : ∀ q ∈ cfgC.workT, q ∈ K0.core.work :=
  StairSquareBChecks.LT48B.sub_of_maskL cfgC.workT K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hLU : ∀ q ∈ cfgC.liveT, q ∈ E0 ∨ q ∈ cfgC.workT :=
  mask_union_mem cfgC.liveT E0 cfgC.workT (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hLB : ∀ q ∈ cfgC.liveT, q ∉ cfgC.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.liveT cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hLS : ∀ q ∈ cfgC.liveT, q ∉ cfgC.src :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.liveT cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hLO : ∀ q ∈ cfgC.liveT, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.liveT K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hSU : ∀ q ∈ cfgC.cleanScratch, q ∈ K0.foldPad ∨ q ∈ K0.core.work :=
  mask_union_mem cfgC.cleanScratch K0.foldPad K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hSB : ∀ q ∈ cfgC.cleanScratch, q ∉ cfgC.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hSS : ∀ q ∈ cfgC.cleanScratch, q ∉ cfgC.src :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hSO : ∀ q ∈ cfgC.cleanScratch, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hSP : ∀ q ∈ cfgC.cleanScratch, q ∉ (ParkCopyS.hostsS E0) :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch (ParkCopyS.hostsS E0) (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hDB : ∀ q ∈ cfgC.dst, q ∉ cfgC.bank :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.dst cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hDS : ∀ q ∈ cfgC.dst, q ∉ cfgC.src :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.dst cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hDO : ∀ q ∈ cfgC.dst, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.dst K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hBO : ∀ q ∈ cfgC.bank, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.bank K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem memory_cfgC_geom_hSrO : ∀ q ∈ cfgC.src, q ∉ K0.core.out :=
  StairSquareBChecks.LT48B.disj_of_maskL cfgC.src K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)

private theorem cfgC_geom :
    124 + (ParkCopyS.hostsS E0).length = cfgC.n ∧
    cfgC.src.length = cfgC.n ∧
    (ParkCopyS.hostsS E0).Nodup ∧
    (∀ h ∈ ParkCopyS.hostsS E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopyS.hostsS E0, h ∉ cfgC.bank ∧ h ∉ cfgC.src ∧ h ∉ cfgC.dst ∧
      h ∉ K0.core.out ∧ h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopyS.hostsS E0 ∧
    (G0 :: cfgC.src ++ cfgC.bank).Nodup ∧
    (∀ q ∈ E0, q ∉ cfgC.bank) ∧
    (∀ q ∈ cfgC.workT, q ∈ K0.core.work) ∧
    (∀ q ∈ cfgC.liveT, (q ∈ E0 ∨ q ∈ cfgC.workT) ∧ q ∉ cfgC.bank ∧ q ∉ cfgC.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgC.cleanScratch, (q ∈ K0.foldPad ∨ q ∈ K0.core.work) ∧ q ∉ cfgC.bank ∧ q ∉ cfgC.src ∧
      q ∉ K0.core.out ∧ q ∉ ParkCopyS.hostsS E0) ∧
    (∀ q ∈ cfgC.dst, q ∉ cfgC.bank ∧ q ∉ cfgC.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgC.bank, q ∉ K0.core.out) ∧
    (∀ q ∈ cfgC.src, q ∉ K0.core.out) ∧
    (G0 ∉ cfgC.bank ∧ G0 ∉ cfgC.dst ∧ G0 ∉ cfgC.liveT ∧ G0 ∉ cfgC.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgC.dst = cfgC.dst.headD 0 ∧
    ControlLoan1589BFFold.eU K0 ∉ ParkCopyS.hostsS E0 := by
  have hS := memory_cfgC_geom_hS
  have hnd := memory_cfgC_geom_hnd
  have hPB := memory_cfgC_geom_hPB
  have hPS := memory_cfgC_geom_hPS
  have hPD := memory_cfgC_geom_hPD
  have hPO := memory_cfgC_geom_hPO
  have hEB := memory_cfgC_geom_hEB
  have hWW := memory_cfgC_geom_hWW
  have hLU := memory_cfgC_geom_hLU
  have hLB := memory_cfgC_geom_hLB
  have hLS := memory_cfgC_geom_hLS
  have hLO := memory_cfgC_geom_hLO
  have hSU := memory_cfgC_geom_hSU
  have hSB := memory_cfgC_geom_hSB
  have hSS := memory_cfgC_geom_hSS
  have hSO := memory_cfgC_geom_hSO
  have hSP := memory_cfgC_geom_hSP
  have hDB := memory_cfgC_geom_hDB
  have hDS := memory_cfgC_geom_hDS
  have hDO := memory_cfgC_geom_hDO
  have hBO := memory_cfgC_geom_hBO
  have hSrO := memory_cfgC_geom_hSrO
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1,
    fun h hh => ⟨hPB h hh, hPS h hh, hPD h hh, hPO h hh, hS.2.2.2.2.1 h hh⟩,
    hS.2.2.2.2.2.1, hnd, hEB, hWW,
    fun q hq => ⟨hLU q hq, hLB q hq, hLS q hq, hLO q hq⟩,
    fun q hq => ⟨hSU q hq, hSB q hq, hSS q hq, hSO q hq, hSP q hq⟩,
    fun q hq => ⟨hDB q hq, hDS q hq, hDO q hq⟩, hBO, hSrO,
    hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2⟩

private theorem e0_dis_bodyA : ∀ q ∈ E0, q ∉ wires bodyA := fun q hq hw => by
  have hs := bodyA_ok.support hw
  rcases Finset.mem_insert.mp hs with rfl | hmem
  · exact (by rw [E0_eq, D0_eq]; decide +kernel : D0 ∉ E0) hq
  · exact hext.away q hq (List.mem_toFinset.mp hmem)

private theorem e0_dis_bodyB : ∀ q ∈ E0, q ∉ wires bodyB := fun q hq hw =>
  hext.away q hq (List.mem_toFinset.mp (bodyB_ok.support hw))

private theorem e0_dis_bodyC : ∀ q ∈ E0, q ∉ wires bodyC := fun q hq hw => by
  have hs := bodyC_ok.support hw
  rcases Finset.mem_insert.mp hs with rfl | hmem
  · exact (by rw [E0_eq, D0_eq]; decide +kernel : D0 ∉ E0) hq
  · exact hext.away q hq (List.mem_toFinset.mp hmem)

private theorem eU_zero_of_prod0 (b : BasisState) (hp0 : regValue K0.core.product b = 0) :
    b (ControlLoan1589BFFold.eU K0) = false := by
  have hm : ControlLoan1589BFFold.eU K0 ∈ K0.core.product := by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  exact (regValue_zero _ _).mp hp0 _ hm

private theorem prod_eq_of_take256 (b : BasisState) (hp256 : b (K0.core.product.getD 256 0) = false)
    (hp257 : b (K0.core.product.getD 257 0) = false) :
    regValue K0.core.product b = regValue (K0.core.product.take 256) b := by
  have hl : K0.core.product.length = 258 := hwK.core.product
  have hdrop : K0.core.product.drop 256 = [K0.core.product.getD 256 0, K0.core.product.getD 257 0] := by
    apply List.ext_getElem (by simp [hl])
    intro i hi1 hi2
    have hi : i = 0 ∨ i = 1 := by simp [hl] at hi1; omega
    rcases hi with rfl | rfl <;> simp [List.getD_eq_getElem?_getD, hl]
  have h0 : regValue [K0.core.product.getD 256 0, K0.core.product.getD 257 0] b = 0 := by
    simp only [regValue, List.foldr_cons, List.foldr_nil, hp256, hp257]; rfl
  conv_lhs => rw [← List.take_append_drop 256 K0.core.product, regValue_append, hdrop, h0]
  simp

theorem brA_run_eq (t : State) (m : List Bool) (pre : BranchPre t) :
    run brA m t = run (recBrA bodyA) m t := by
  have g := cfgA_geom
  have h128 : regValue K0.core.low t.basis < 2 ^ 128 := by
    simpa [K0.core.low_length hwK.core] using regValue_lt K0.core.low t.basis
  let M := if t.basis G0 then regValue K0.core.low t.basis else 0
  let O := regValue K0.core.out t.basis
  let V := A161Low4Offsets.resAFlow (M ^ 2) O (t.basis G0)
  have hMlt : M < 2 ^ 128 := by dsimp only [M]; split_ifs <;> omega
  have hRec := A161Low4Branch.swapped_correct K0 hwK E0 G0 controlND
    (regValue K0.core.low t.basis) O pre.outLt t m rfl rfl pre.prod0 pre.clean pre.sum0 hext pre.ext0
    D0 (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (B3CarryPort.pool1540_facts L0 hw0 hn0).2.1 pre.d0
    bodyA bodyA_ok.support bodyA_ok.eUfree bodyA_ok.frame
  have hNew := withSplitPark_correct cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA V
    g.1 (by decide) g.2.1 g.2.2.1 g.2.2.2.1
    (fun h hh => (g.2.2.2.2.1 h hh).1) (fun h hh => (g.2.2.2.2.1 h hh).2.1)
    (fun h hh => (g.2.2.2.2.1 h hh).2.2.1) (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.1)
    g.2.2.2.2.2.1 (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    (fun q hq => Or.inl (g.2.2.2.2.2.2.2.2.1 q hq)) e0_dis_bodyA bodyA_avoids_workTA (fun _ => bodyA_ok.eUfree)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun s0 m0 hd0 hT0 hSc0 hi0 heu0 he0 =>
      cfg128_zeros cfgA cfgA_valid rfl g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        (by simp [SplitCfg.T, cfgA, List.take_take]) rfl rfl _
        (fun h hh => by simp only [ParkCopy10.hosts10, List.mem_append, List.mem_singleton] at hh; exact hh)
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2⟩
        s0 m0 hd0 hT0 hSc0 hi0 heu0 he0)
    t m pre.clean
    ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp pre.prod0 q (List.mem_of_mem_take hq)))
    pre.ext0 pre.d0 (fun _ => eU_zero_of_prod0 t.basis pre.prod0)
    (fun t' m' hdst hkeep => by
      have h256_dis : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
          K0.core.cin, K0.core.normFlag, K0.core.modFlag, K0.core.product.getD 256 0, K0.core.product.getD 257 0,
          K0.core.sumCarry, D0, G0], q ∉ cfgA.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgA_fast, K0_eq, D0_eq, G0_eq]; decide +kernel)
      have h256_in : K0.core.product.getD 256 0 ∈ K0.core.product ∧ K0.core.product.getD 257 0 ∈ K0.core.product :=
        ⟨DiagSq.getD_in _ 256 (by rw [hwK.core.product]; decide), DiagSq.getD_in _ 257 (by rw [hwK.core.product]; decide)⟩
      have hprod : regValue K0.core.product t'.basis = M ^ 2 := by
        rw [prod_eq_of_take256 t'.basis
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.1))
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.2))]
        exact hdst
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.work,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.productHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.outHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.workHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.cin,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.normFlag,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := hkeep G0 (h256_dis _ (by simp))
      have hout : regValue K0.core.out t'.basis = O :=
        regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))
      have hfr := bodyA_ok.frame t'.basis M hMlt hprod hpc ((hkeep _ (h256_dis _ (by simp))).trans pre.sum0) O pre.outLt
        (fun hg => by rw [hG] at hg; simp [M, hg]) ((hkeep _ (h256_dis _ (by simp))).trans pre.d0)
        t' m' ⟨hout, fun _ _ => rfl⟩
      rw [hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  exact state_eq_of_out _ _ (hNew.1.trans hRec.1.symm)
    (by simpa [V, M, O, recBrA, A161Low4Branch.branch] using hNew.2.1.trans hRec.2.1.symm)
    (fun q hq => (hNew.2.2 q hq).trans (hRec.2.2 q hq).symm)

theorem brB_run_eq (t : State) (m : List Bool) (pre : BranchPre t) :
    run brB m t = run (recBrB bodyB) m t := by
  have g := cfgB_geom
  have h128 : regValue K0.core.high t.basis < 2 ^ 128 := by
    simpa [K0.core.high_length hwK.core] using regValue_lt K0.core.high t.basis
  let M := if t.basis G0 then regValue K0.core.high t.basis else 0
  let O := regValue K0.core.out t.basis
  let V := ControlLoan1589BFFold.resBF (M ^ 2) O (t.basis G0)
  have hMlt : M < 2 ^ 128 := by dsimp only [M]; split_ifs <;> omega
  have hRec := StairSquareAssembly.recBrB_correct bodyB bodyB_ok (regValue K0.core.high t.basis) O
    pre.outLt t m rfl rfl pre.prod0 pre.clean pre.sum0 pre.ext0
  have hNew := withSplitPark_correct cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB V
    g.1 (by decide) g.2.1 g.2.2.1 g.2.2.2.1
    (fun h hh => (g.2.2.2.2.1 h hh).1) (fun h hh => (g.2.2.2.2.1 h hh).2.1)
    (fun h hh => (g.2.2.2.2.1 h hh).2.2.1) (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.1)
    g.2.2.2.2.2.1 (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.1 e0_dis_bodyB bodyB_avoids_workTB
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun s0 m0 hd0 hT0 hSc0 hi0 heu0 he0 =>
      cfg128_zeros cfgB cfgB_valid rfl g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        (by simp [SplitCfg.T, cfgB, List.take_take]) rfl rfl _ (fun _ hh => Or.inl hh)
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1⟩
        s0 m0 hd0 hT0 hSc0 hi0 heu0 he0)
    t m pre.clean
    ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp pre.prod0 q (List.mem_of_mem_take hq)))
    pre.ext0 pre.d0 (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2)
    (fun t' m' hdst hkeep => by
      have h256_dis : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
          K0.core.cin, K0.core.normFlag, K0.core.modFlag, K0.core.product.getD 256 0, K0.core.product.getD 257 0,
          K0.core.sumCarry, G0], q ∉ cfgB.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgB_fast, K0_eq, G0_eq]; decide +kernel)
      have h256_in : K0.core.product.getD 256 0 ∈ K0.core.product ∧ K0.core.product.getD 257 0 ∈ K0.core.product :=
        ⟨DiagSq.getD_in _ 256 (by rw [hwK.core.product]; decide), DiagSq.getD_in _ 257 (by rw [hwK.core.product]; decide)⟩
      have hprod : regValue K0.core.product t'.basis = M ^ 2 := by
        rw [prod_eq_of_take256 t'.basis
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.1))
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.2))]
        exact hdst
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.work,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.productHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.outHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.workHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.cin,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.normFlag,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := hkeep G0 (h256_dis _ (by simp))
      have hout : regValue K0.core.out t'.basis = O :=
        regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))
      have hhi : regValue K0.core.high t'.basis = regValue K0.core.high t.basis :=
        regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.1 hq))
      have hg0 : t'.basis G0 = false → M = 0 := fun hg => by rw [hG] at hg; simp [M, hg]
      have hfr := bodyB_ok.frame t'.basis M hMlt hprod hpc ((hkeep _ (h256_dis _ (by simp))).trans pre.sum0) O pre.outLt
        hg0 (by rw [hG, hhi]) t' m' ⟨hout, fun _ _ => rfl⟩
      rw [ControlLoan1589BFFold.bO4_eq M O (t'.basis G0) hMlt hg0 pre.outLt, hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  exact state_eq_of_out _ _ (hNew.1.trans hRec.1.symm)
    (by simpa [V, M, O] using hNew.2.1.trans hRec.2.1.symm)
    (fun q hq => (hNew.2.2 q hq).trans (hRec.2.2 q hq).symm)

theorem brC_run_eq (t : State) (m : List Bool) (pre : BranchPre t) :
    run brC m t = run (recBrC bodyC) m t := by
  have g := cfgC_geom
  have nd := (List.nodup_cons.mp controlND).2
  have dis := K0.measured_sum_disjoint nd
  have ctrlAway : G0 ∉ K0.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp controlND G0
    have pos := List.count_pos_iff.mpr bad
    have sumBound := K0.measured_sum_count G0
    simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, List.count_append, List.count_cons,
      List.count_nil, beq_self_eq_true, if_true] at h sumBound
    omega
  set A := regValue K0.core.low t.basis
  set B := regValue K0.core.sum t.basis
  set O := regValue K0.core.out t.basis
  have hLowLt : A < 2 ^ 128 := by
    simpa [A, K0.core.low_length hwK.core] using regValue_lt K0.core.low t.basis
  have hSumEq : B = regValue K0.core.high t.basis := by
    simp [B, CuccaroStreamedSquareLayout.sum, regValue_append, regValue, pre.sum0]
  have hHiLt : regValue K0.core.high t.basis < 2 ^ 128 := by
    simpa [K0.core.high_length hwK.core] using regValue_lt K0.core.high t.basis
  have hSumBd : A + B < 2 ^ 129 := by rw [hSumEq]; omega
  let midNew := withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC
  obtain ⟨r1, mC, eC⟩ := kseq (OwnDiagAll12Square.gPrep K0 ++ midNew) (OwnDiagAll12Square.gClear K0) m t
  obtain ⟨mP, mM, eM⟩ := kseq (OwnDiagAll12Square.gPrep K0) midNew r1 t
  have hbrC : run brC m t = run (OwnDiagAll12Square.gClear K0) mC (run midNew mM (run (OwnDiagAll12Square.gPrep K0) mP t)) := by
    change run ((OwnDiagAll12Square.gPrep K0 ++ midNew) ++ OwnDiagAll12Square.gClear K0) m t = _
    rw [eC, eM]
  have hprep := OwnDiagAll12Square.gPrep_frame K0 hwK nd t.basis A B rfl hSumBd
    (PairClean.corePad K0 t.basis pre.clean) pre.clean.cin pre.clean.work t mP ⟨rfl, fun _ _ => rfl⟩
  generalize hu : run (OwnDiagAll12Square.gPrep K0) mP t = u at hbrC hprep ⊢
  have u_prod0 : regValue K0.core.product u.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans pre.prod0
  have u_out : regValue K0.core.out u.basis = O :=
    regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))
  have u_ctrl : u.basis G0 = t.basis G0 := hprep.2.2 G0 ctrlAway
  have u_clean : K0.PairClean u.basis := by
    have keep (q : Wire) (hq : q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh,
        K0.core.workHigh, K0.core.cin, K0.core.normFlag, K0.core.modFlag]) : u.basis q = t.basis q :=
      hprep.2.2 q (K0.measured_sum_aux_away nd q hq)
    exact ⟨(regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans pre.clean.pad,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans pre.clean.work,
      (keep _ (by simp)).trans pre.clean.productHigh, (keep _ (by simp)).trans pre.clean.outHigh,
      (keep _ (by simp)).trans pre.clean.workHigh, (keep _ (by simp)).trans pre.clean.cin,
      (keep _ (by simp)).trans pre.clean.normFlag, (keep _ (by simp)).trans pre.clean.modFlag⟩
  have u_ext0 : regValue E0 u.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => hext.away q hq (OwnDiagAll12Square.sum_in K0 G0 q bad)))).trans pre.ext0
  have u_d0 : u.basis D0 = false :=
    (hprep.2.2 D0 (fun bad => (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (OwnDiagAll12Square.sum_in K0 G0 D0 bad))).trans pre.d0
  let M := if t.basis G0 then A + B else 0
  let V := C163Low4Offsets.resCFlow (t.basis G0) (M ^ 2) O
  have hM_eq : (if u.basis G0 = true then regValue cfgC.src u.basis else 0) = M := by
    change (if u.basis G0 = true then regValue K0.core.sum u.basis else 0) = M
    rw [u_ctrl, hprep.2.1]
  have used := withSplitPark_correct cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC V
    g.1 (by decide) g.2.1 g.2.2.1 g.2.2.2.1
    (fun h hh => (g.2.2.2.2.1 h hh).1) (fun h hh => (g.2.2.2.2.1 h hh).2.1)
    (fun h hh => (g.2.2.2.2.1 h hh).2.2.1) (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.1)
    g.2.2.2.2.2.1 (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    (fun q hq => Or.inl (g.2.2.2.2.2.2.2.2.1 q hq)) e0_dis_bodyC bodyC_avoids_workTC
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    cfgC_zeros u mM u_clean u_prod0 u_ext0 u_d0
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (fun t' m' hdst hkeep => by
      have haux : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
            K0.core.cin, K0.core.normFlag, K0.core.modFlag, D0, G0], q ∉ cfgC.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgC_fast, K0_eq, D0_eq, G0_eq]; decide +kernel)
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (haux q (by simp [hq])))).trans u_clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (haux q (by simp [hq])))).trans u_clean.work,
        (hkeep _ (haux _ (by simp))).trans u_clean.productHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.outHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.workHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.cin,
        (hkeep _ (haux _ (by simp))).trans u_clean.normFlag,
        (hkeep _ (haux _ (by simp))).trans u_clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := (hkeep G0 (haux _ (by simp))).trans u_ctrl
      have hout : regValue K0.core.out t'.basis = O :=
        (regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))).trans u_out
      have hdstM : regValue K0.core.product t'.basis = M ^ 2 := by rw [← hM_eq]; exact hdst
      have hfr := bodyC_ok.frame t'.basis M hdstM hpc (fun hg => by rw [hG] at hg; simp [M, hg])
        ((hkeep _ (haux _ (by simp))).trans u_d0) O pre.outLt t' m' ⟨hout, fun _ _ => rfl⟩
      rw [hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  change (run midNew mM u).phase = u.phase ∧ regValue K0.core.out (run midNew mM u).basis = V ∧
    ∀ q, q ∉ K0.core.out → (run midNew mM u).basis q = u.basis q at used
  generalize hv : run midNew mM u = v at hbrC used ⊢
  let restoreBase : BasisState := fun q => if q ∈ K0.core.out then v.basis q else t.basis q
  have lowOutAway (q : Wire) (hq : q ∈ K0.core.low) : q ∉ K0.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, List.count_append, List.count_cons, List.count_nil] at h
    omega
  have lowRestore : regValue K0.core.low restoreBase = A :=
    regValue_congr _ _ _ (fun q hq => by simp [restoreBase, lowOutAway q hq])
  have padRestore : regValue K0.core.pad restoreBase = 0 :=
    (regValue_congr _ _ _ (fun q hq => by
      have away := (K0.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad, hq])).2
      simp [restoreBase, away])).trans (PairClean.corePad K0 t.basis pre.clean)
  have cinRestore : restoreBase K0.core.cin = false := by
    have away := (K0.pairAuxAway nd K0.core.cin (by simp)).2
    simp [restoreBase, away, pre.clean.cin]
  have workRestore : regValue K0.core.work restoreBase = 0 :=
    (regValue_congr _ _ _ (fun q hq => by
      have away := (K0.pairAuxAway nd q (by simp [hq])).2
      simp [restoreBase, away])).trans pre.clean.work
  have clearPre : SquareFrame K0.core.sum restoreBase (A + B) v.basis := by
    refine ⟨(regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans hprep.2.1, ?_⟩
    intro q hq
    by_cases outSite : q ∈ K0.core.out
    · simp [restoreBase, outSite]
    · simp only [restoreBase, if_neg outSite]
      exact (used.2.2 q outSite).trans (hprep.2.2 q hq)
  have cleared := OwnDiagAll12Square.gClear_frame K0 hwK nd restoreBase A B lowRestore hSumBd padRestore cinRestore workRestore v mC clearPre
  generalize hout : run (OwnDiagAll12Square.gClear K0) mC v = out at hbrC cleared ⊢
  have hNew : out.phase = t.phase ∧ regValue K0.core.out out.basis = V ∧ ∀ q, q ∉ K0.core.out → out.basis q = t.basis q := by
    refine ⟨cleared.1.trans (used.1.trans hprep.1), ?_, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => by
        have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
        simpa [restoreBase, hq] using same)).trans used.2.1
    · intro q hq
      by_cases sumSite : q ∈ K0.core.sum
      · exact (regValue_eq_iff K0.core.sum out.basis t.basis).mp cleared.2.1 q sumSite
      · have same := cleared.2.2 q sumSite
        simpa [restoreBase, hq] using same
  have hRec := SumSavedCBranch.branch_correct K0 hwK E0 G0 controlND A B O pre.outLt t m rfl rfl hSumBd rfl
    pre.prod0 pre.clean hext pre.ext0 D0 (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (B3CarryPort.pool1540_facts L0 hw0 hn0).2.1
    pre.d0 bodyC bodyC_ok.support bodyC_ok.frame
  rw [hbrC]
  exact state_eq_of_out _ _ (hNew.1.trans hRec.1.symm)
    (by simpa [V, M, recBrC] using hNew.2.1.trans hRec.2.1.symm)
    (fun q hq => (hNew.2.2 q hq).trans (hRec.2.2 q hq).symm)

/-- Top-level core correctness of the split-65 concrete square core. -/
theorem coreOK : CoreOK L0 (coreN brC brB brA) :=
  coreN_coreOK bodyA bodyB bodyC brC brB brA bodyA_ok bodyB_ok bodyC_ok brC_run_eq brB_run_eq brA_run_eq

/-! ### Exact Toffoli, measurement, and gate-slot counts -/

theorem brA_counts :
    toffoliCount brA + 316 = toffoliCount (recBrA A109SignResearch.body) ∧
    measurementCount brA + 197 = measurementCount (recBrA A109SignResearch.body) := by
  have hMakeDelta := cfgA_make_delta
  have hMakeMeasure := cfg_make_measurements cfgA cfgA_valid
  have hDelta := cfgA_clear_delta
  have hMeasure := cfg_clear_measurements cfgA cfgA_valid
  have hk := cfg_counts_H cfgA cfgA_valid rfl K0.core.low (K0.core.product.take 256)
    (K0.core.low_length hwK.core) (by rw [List.length_take, hwK.core.product]; decide)
  have hb := bodyA_counts
  have hc := InnerLinearCopy.copy_counts118 G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.low.take 118) ((K0.inputBank.take K0.core.low.length).take 118)
    (by simp [K0.core.low_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.low_length hwK.core])
  have hbl : K0.core.low.length = 128 := K0.core.low_length hwK.core
  dsimp only at hk
  simp only [brA, withSplitPark, recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10,
    ParkCopy10.pA, ParkCopy10.pM, ParkCopy10.pE1, ParkCopy10.pD, ParkCopy10.pMI, ParkCopy10.pB,
    ParkCopy10.pC1, ParkCopy10.pMO, ParkCopy10.pCL, ParkCopy10.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgA, hbl, toffoliCount_append, measurementCount_append,
    renameProgram_counts] at hk hc hDelta hMeasure hMakeDelta hMakeMeasure ⊢
  exact ⟨by clear * - hk hb hc hDelta hMeasure hMakeDelta hMakeMeasure; omega, by clear * - hk hb hc hDelta hMeasure hMakeDelta hMakeMeasure; omega⟩

theorem brB_counts :
    toffoliCount brB + 306 = toffoliCount (recBrB B95PaddedResearch.body) ∧
    measurementCount brB + 197 = measurementCount (recBrB B95PaddedResearch.body) := by
  have hMakeDelta := cfgB_make_delta
  have hMakeMeasure := cfg_make_measurements cfgB cfgB_valid
  have hDelta := cfgB_clear_delta
  have hMeasure := cfg_clear_measurements cfgB cfgB_valid
  have hk := cfg_counts_H cfgB cfgB_valid rfl K0.core.high (K0.core.product.take 256)
    (K0.core.high_length hwK.core) (by rw [List.length_take, hwK.core.product]; decide)
  have hb := bodyB_counts
  have hc := InnerLinearCopy.copy_counts G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.high.take 119) ((K0.inputBank.take K0.core.high.length).take 119)
    (by simp [K0.core.high_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.high_length hwK.core])
  have hbl : K0.core.high.length = 128 := K0.core.high_length hwK.core
  dsimp only at hk
  simp only [brB, withSplitPark, recBrB, ParkCopy.withLowK2P,
    ParkCopy.pA, ParkCopy.pM, ParkCopy.pE1, ParkCopy.pD, ParkCopy.pMI, ParkCopy.pB,
    ParkCopy.pC1, ParkCopy.pMO, ParkCopy.pCL, ParkCopy.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgB, hbl, toffoliCount_append, measurementCount_append,
    renameProgram_counts] at hk hc hDelta hMeasure hMakeDelta hMakeMeasure ⊢
  exact ⟨by clear * - hk hb hc hDelta hMeasure hMakeDelta hMakeMeasure; omega, by clear * - hk hb hc hDelta hMeasure hMakeDelta hMakeMeasure; omega⟩

theorem brC_counts :
    toffoliCount brC + 312 = toffoliCount (recBrC C105SignResearch.body) ∧
    measurementCount brC + 195 = measurementCount (recBrC C105SignResearch.body) := by
  have hMakeDelta := cfgC_make_delta
  have hMakeMeasure := cfg_make_measurements cfgC cfgC_valid
  have hDelta := cfgC_clear_delta
  have hMeasure := cfg_clear_measurements cfgC cfgC_valid
  have hk := cfg_counts_S cfgC cfgC_valid rfl K0.core.sum K0.core.product
    (K0.core.sum_length hwK.core) hwK.core.product
  have hb := bodyC_counts
  have srcCount (q : Wire) : K0.core.sum.count q ≤ (K0.core.y ++ [K0.core.sumCarry]).count q := by
    have h1 := (List.take_sublist 128 (K0.core.y.drop 128)).count_le q
    have h2 := (List.drop_sublist 128 K0.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum, CuccaroStreamedSquareLayout.high, List.count_append] at h1 ⊢; omega
  have hall := LowZero18LowK.kg_nodup K0 G0 controlND E0 K0.core.sum K0.core.product srcCount (fun _ => le_rfl) hext.nodup hext.away
  have sp := LowZero18LowK.kg_spec K0 hwK E0 K0.core.sum K0.core.product
    (by rw [K0.core.sum_length hwK.core]; decide) (by rw [K0.core.sum_length hwK.core])
    (by rw [K0.core.sum_length hwK.core, hwK.core.product]) hext.len hall
  have hcl := SumSavedSquare.clear_counts K0 hwK E0 K0.core.sum K0.core.product hext.len (K0.core.sum_length hwK.core) sp hall
  have hbl : K0.core.sum.length = 129 := K0.core.sum_length hwK.core
  dsimp only at hk
  simp only [brC, withSplitPark, recBrC, SumSavedCBranch.branch, SumSavedPark.withLowK2S, SumSavedPark.pCL,
    ParkCopyS.pA, ParkCopyS.pM, ParkCopyS.pE1, ParkCopyS.pD, ParkCopyS.pMI, ParkCopyS.pB,
    ParkCopyS.pC1, ParkCopyS.pMO, ParkCopyS.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgC, hbl, toffoliCount_append, measurementCount_append,
    renameProgram_counts] at hk hcl hDelta hMeasure hMakeDelta hMakeMeasure ⊢
  exact ⟨by clear * - hk hb hcl hDelta hMeasure hMakeDelta hMakeMeasure; omega, by clear * - hk hb hcl hDelta hMeasure hMakeDelta hMakeMeasure; omega⟩

theorem square_counts (k : Fp) :
    toffoliCount (squareN brC brB brA k) + 934 = toffoliCount (A161Generic.squareEntry L0 k) ∧
    measurementCount (squareN brC brB brA k) + 589 = measurementCount (A161Generic.squareEntry L0 k) := by
  have cA := brA_counts; have cB := brB_counts; have cC := brC_counts
  have e1 : toffoliCount (StairSquareEntryR.entryRH (k - (C163Low4Offsets.delta : Fp))) =
        toffoliCount (E1ReflectedPlacement.entryR L0 (k - (C163Low4Offsets.delta : Fp))) ∧
      measurementCount (StairSquareEntryR.entryRH (k - (C163Low4Offsets.delta : Fp))) =
        measurementCount (E1ReflectedPlacement.entryR L0 (k - (C163Low4Offsets.delta : Fp))) :=
    StairSquareEntryR.entryRH_counts _
  rw [recordSquare_eq, SumSavedB95Square.program, StairSquareAssembly.fastCore_eq, StairSquareFinal.branchBF760_rec]
  simp only [squareN, placedN, coreN, SquareCarryLoan719BF.place,
    toffoliCount_append, measurementCount_append, renameProgram_counts]
  exact ⟨by clear * - cA cB cC e1; omega, by clear * - cA cB cC e1; omega⟩

theorem brA_slots_le :
    Challenge.gateSlots brA ≤ Challenge.gateSlots (recBrA A109SignResearch.body) + 1830000 := by
  have hk := cfg_slots_bound cfgA cfgA_valid
  have hb := bodyA_slots
  have hc := InnerLinearCopy.copy_slots118 G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.low.take 118) ((K0.inputBank.take K0.core.low.length).take 118)
    (by simp [K0.core.low_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.low_length hwK.core])
  have hbl : K0.core.low.length = 128 := K0.core.low_length hwK.core
  simp only [brA, withSplitPark, recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10,
    ParkCopy10.pA, ParkCopy10.pM, ParkCopy10.pE1, ParkCopy10.pD, ParkCopy10.pMI, ParkCopy10.pB,
    ParkCopy10.pC1, ParkCopy10.pMO, ParkCopy10.pCL, ParkCopy10.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgA, hbl, Challenge.gateSlots_append, Baselines.rename_gateSlots] at hk hc ⊢
  clear * - hk hb hc; omega

theorem brB_slots_le :
    Challenge.gateSlots brB ≤ Challenge.gateSlots (recBrB B95PaddedResearch.body) + 1830000 := by
  have hk := cfg_slots_bound cfgB cfgB_valid
  have hb := bodyB_slots
  have hc := InnerLinearCopy.copy_slots G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.high.take 119) ((K0.inputBank.take K0.core.high.length).take 119)
    (by simp [K0.core.high_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.high_length hwK.core])
  have hbl : K0.core.high.length = 128 := K0.core.high_length hwK.core
  simp only [brB, withSplitPark, recBrB, ParkCopy.withLowK2P,
    ParkCopy.pA, ParkCopy.pM, ParkCopy.pE1, ParkCopy.pD, ParkCopy.pMI, ParkCopy.pB,
    ParkCopy.pC1, ParkCopy.pMO, ParkCopy.pCL, ParkCopy.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgB, hbl, Challenge.gateSlots_append, Baselines.rename_gateSlots] at hk hc ⊢
  clear * - hk hb hc; omega

theorem brC_slots_le :
    Challenge.gateSlots brC ≤ Challenge.gateSlots (recBrC C105SignResearch.body) + 1830000 := by
  have hk := cfg_slots_bound cfgC cfgC_valid
  have hb := bodyC_slots
  have hbl : K0.core.sum.length = 129 := K0.core.sum_length hwK.core
  simp only [brC, withSplitPark, recBrC, SumSavedCBranch.branch, SumSavedPark.withLowK2S, SumSavedPark.pCL,
    ParkCopyS.pA, ParkCopyS.pM, ParkCopyS.pE1, ParkCopyS.pD, ParkCopyS.pMI, ParkCopyS.pB,
    ParkCopyS.pC1, ParkCopyS.pMO, ParkCopyS.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgC, hbl, Challenge.gateSlots_append, Baselines.rename_gateSlots] at hk ⊢
  clear * - hk hb; omega

theorem square_slots_le (k : Fp) :
    Challenge.gateSlots (squareN brC brB brA k) ≤ Challenge.gateSlots (A161Generic.squareEntry L0 k) + 5490000 := by
  have sA := brA_slots_le; have sB := brB_slots_le; have sC := brC_slots_le
  have e := squareN_slots brC brB brA k
  have r : Challenge.gateSlots (A161Generic.squareEntry L0 k) =
      Challenge.gateSlots (recBrC C105SignResearch.body) + Challenge.gateSlots (recBrB B95PaddedResearch.body) +
        Challenge.gateSlots (recBrA A109SignResearch.body) +
        Challenge.gateSlots (E1ReflectedPlacement.entryR L0 (k - (C163Low4Offsets.delta : Fp))) := by
    rw [recordSquare_eq, SumSavedB95Square.program, StairSquareAssembly.fastCore_eq, StairSquareFinal.branchBF760_rec]
    simp only [SquareCarryLoan719BF.place, Challenge.gateSlots_append, Baselines.rename_gateSlots]
  rw [e, r]; clear * - sA sB sC; omega

/-! ### Physicality, wire support, and hole avoidance -/

private theorem dummies_physical (hs : List Wire) : GatePhysical (ParkCopy.dummies hs) := by
  rw [GatePhysical]
  intro x hx
  simp only [ParkCopy.dummies, List.mem_map] at hx
  rcases hx with ⟨a, _, rfl⟩
  simp [RecordedQuantum.PhysicalInstr]

private theorem dummies_wires (hs : List Wire) : wires (ParkCopy.dummies hs) ⊆ hs.toFinset := by
  induction hs with
  | nil => simp [ParkCopy.dummies, wires]
  | cons a hs ih =>
    intro q hq
    rw [ParkCopy.dummies, List.map_cons, wires] at hq
    rcases Finset.mem_union.mp hq with h | h
    · simp [Instr.wires, ECDSAAdd.correctionWires] at h; simp [h]
    · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (ih h)))

private theorem move_physical (a b : List Wire) (hnd : (a ++ b).Nodup) :
    GatePhysical (ParkCopy.move a b) := by
  have hnd' : (b ++ a).Nodup := (List.perm_append_comm.nodup_iff).mp hnd
  simp only [ParkCopy.move, gatePhysical_append]
  exact ⟨copyRegister_physical none a b hnd (by simp), copyRegister_physical none b a hnd' (by simp)⟩

private theorem move_wires (a b : List Wire) : wires (ParkCopy.move a b) ⊆ (a ++ b).toFinset := by
  intro q hq
  simp only [ParkCopy.move, wires_append, Finset.mem_union] at hq
  rcases hq with h | h
  · have := copyRegister_wires_subset none a b h
    simpa [Option.toList_none] using this
  · have := copyRegister_wires_subset none b a h
    simp only [Option.toList_none, List.nil_append, List.mem_toFinset, List.mem_append] at this ⊢
    exact this.symm

private theorem withSplitPark_physical (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program) (hbody : GatePhysical body)
    (hkLen : keepBits + parkHosts.length = c.n) (hkPos : 0 < keepBits) (hsrcLen : c.src.length = c.n)
    (hParkNd : parkHosts.Nodup) (hParkDisBank : ∀ h ∈ parkHosts, h ∉ c.bank)
    (hSrcDis : (G0 :: c.src ++ c.bank).Nodup)
    (hCacheNotBank : LowZero18Square.cacheWire K0 c.dst ∉ c.bank) :
    GatePhysical (withSplitPark c keepBits parkHosts body) := by
  have hbankLen : c.bank.length = c.n := v.bankLen
  have hndSB : (c.src ++ c.bank).Nodup := (List.nodup_cons.mp hSrcDis).2
  have hG0B : ∀ x ∈ some G0, x ∉ c.bank := fun x hx => by
    cases Option.some.inj hx; exact fun hb => (List.nodup_cons.mp hSrcDis).1 (List.mem_append_right _ hb)
  have hndMask : (G0 :: c.src.take keepBits ++ c.bank.take keepBits).Nodup :=
    list_nodup_of_count_le hSrcDis (fun q => by
      have a := (List.take_sublist keepBits c.src).count_le q
      have b := (List.take_sublist keepBits c.bank).count_le q
      simp only [List.count_cons, List.count_append]; omega)
  have hndMP : (c.bank.drop keepBits ++ parkHosts).Nodup :=
    List.nodup_append.mpr ⟨((List.nodup_append.mp hndSB).2.1).sublist (List.drop_sublist _ _), hParkNd,
      fun q hq r hr heq => hParkDisBank r hr (heq ▸ List.mem_of_mem_drop hq)⟩
  have hndPM : (parkHosts ++ c.bank.drop keepBits).Nodup := (List.perm_append_comm.nodup_iff).mp hndMP
  have hcfg := cfg_physical c v
  have hHeadIn : (c.bank.take keepBits).headD 0 ∈ c.bank := by
    rw [ParkCopy.headD_take c.bank keepBits hkPos]
    have hpos : 0 < c.bank.length := by omega
    have h0 : c.bank.headD 0 = c.bank.getD 0 0 := by cases c.bank <;> simp
    rw [h0]; exact DiagSq.getD_in c.bank 0 hpos
  have hC1 : GatePhysical (CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 c.dst)
      (c.src.take keepBits) (c.bank.take keepBits)) :=
    CachedSquareCopy.physical G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits)
      (fun heq => hCacheNotBank (heq ▸ hHeadIn))
      (copyRegister_physical (some G0) (c.src.take keepBits) (c.bank.take keepBits)
        (List.nodup_cons.mp hndMask).2 (fun x hx hb => hG0B x hx (List.mem_of_mem_take hb)))
  have hB : GatePhysical (renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)) :=
    gatePhysical_rename _ (LowZero18Square.foldPerm K0 E0).injective _
      (gatePhysical_rename _ (R2SqEp760.sqSwap K0 E0).injective _ hbody)
  simp only [withSplitPark, gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨copyRegister_physical (some G0) c.src c.bank hndSB hG0B,
    hcfg.1⟩, eraseMask_physical G0 _ _⟩,
    dummies_physical parkHosts⟩, move_physical _ _ hndMP⟩, hB⟩, hC1⟩,
    move_physical _ _ hndPM⟩, hcfg.2⟩, eraseMask_physical G0 c.src c.bank⟩

theorem brA_physical : GatePhysical brA :=
  withSplitPark_physical cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA bodyA_physical
    cfgA_geom.1 (by decide) cfgA_geom.2.1 cfgA_geom.2.2.1 (fun h hh => (cfgA_geom.2.2.2.2.1 h hh).1)
    cfgA_geom.2.2.2.2.2.2.1 (by simp only [cfgA_fast, SplitCfg.bank_fast, K0_eq]; decide +kernel)

theorem brB_physical : GatePhysical brB :=
  withSplitPark_physical cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB bodyB_physical
    cfgB_geom.1 (by decide) cfgB_geom.2.1 cfgB_geom.2.2.1 (fun h hh => (cfgB_geom.2.2.2.2.1 h hh).1)
    cfgB_geom.2.2.2.2.2.2.1 (by simp only [cfgB_fast, SplitCfg.bank_fast, K0_eq]; decide +kernel)

theorem brC_physical : GatePhysical brC := by
  have hr := StairSquareFinal.record_branches_physical.1
  simp only [recBrC, SumSavedCBranch.branch, gatePhysical_append] at hr
  simp only [brC, gatePhysical_append]
  exact ⟨⟨hr.1.1, withSplitPark_physical cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC bodyC_physical
    cfgC_geom.1 (by decide) cfgC_geom.2.1 cfgC_geom.2.2.1 (fun h hh => (cfgC_geom.2.2.2.2.1 h hh).1)
    cfgC_geom.2.2.2.2.2.2.1 (by simp only [cfgC_fast, SplitCfg.bank_fast, K0_eq]; decide +kernel)⟩, hr.2⟩

theorem square_physical (k : Fp) : GatePhysical (squareN brC brB brA k) :=
  squareN_physical brC brB brA k brC_physical brB_physical brA_physical

private theorem withSplitPark_support_aux (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program)
    (hSrcAllowed : ∀ q ∈ c.src, q ∈ allowedWires)
    (hParkAllowed : ∀ q ∈ parkHosts, q ∈ allowedWires)
    (hCacheAllowed : LowZero18Square.cacheWire K0 c.dst ∈ allowedWires) :
    wires (withSplitPark c keepBits parkHosts body) ⊆
      wires (renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)) ∪ allowedWires.toFinset := by
  have hG0A : G0 ∈ allowedWires :=
    sub_allowedWires [G0] (fun q hq => by simp [List.mem_singleton.mp hq])
      (fun q hq => by rw [List.mem_singleton.mp hq, G0_eq, hs_lit]; decide +kernel) G0 (by simp)
  have hReal : c.realAll.toFinset ⊆ allowedWires.toFinset := fun q hq =>
    List.mem_toFinset.mpr (v.realAllowed q (List.mem_toFinset.mp hq))
  have hBankA : ∀ q ∈ c.bank, q ∈ allowedWires := fun q hq => v.realAllowed q (by simp [SplitCfg.realAll, hq])
  have hcfg := cfg_support c v
  intro q hq
  simp only [withSplitPark, wires_append, Finset.mem_union] at hq
  rcases hq with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := copyRegister_wires_subset (some G0) c.src c.bank h
    simp only [Option.toList_some, List.singleton_append, List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at w
    rcases w with rfl | w | w
    · exact hG0A
    · exact hSrcAllowed q w
    · exact hBankA q w
  · exact Finset.mem_union_right _ (hReal (hcfg.1 h))
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := eraseMask_wires_subset G0 (c.src.take keepBits) (c.bank.take keepBits) h
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at w
    rcases w with rfl | w | w
    · exact hG0A
    · exact hSrcAllowed q (List.mem_of_mem_take w)
    · exact hBankA q (List.mem_of_mem_take w)
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (hParkAllowed q (List.mem_toFinset.mp (dummies_wires _ h))))
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := move_wires (c.bank.drop keepBits) parkHosts h
    simp only [List.mem_toFinset, List.mem_append] at w
    rcases w with w | w
    · exact hBankA q (List.mem_of_mem_drop w)
    · exact hParkAllowed q w
  · exact Finset.mem_union_left _ h
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := CachedSquareCopy.wires_subset G0 (LowZero18Square.cacheWire K0 c.dst)
      (c.src.take keepBits) (c.bank.take keepBits) h
    rcases Finset.mem_union.mp w with wc | hc
    · have w2 := copyRegister_wires_subset (some G0) (c.src.take keepBits) (c.bank.take keepBits) wc
      simp only [Option.toList_some, List.singleton_append, List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at w2
      rcases w2 with rfl | w2 | w2
      · exact hG0A
      · exact hSrcAllowed q (List.mem_of_mem_take w2)
      · exact hBankA q (List.mem_of_mem_take w2)
    · rw [Finset.mem_singleton.mp hc]; exact hCacheAllowed
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := move_wires parkHosts (c.bank.drop keepBits) h
    simp only [List.mem_toFinset, List.mem_append] at w
    rcases w with w | w
    · exact hParkAllowed q w
    · exact hBankA q (List.mem_of_mem_drop w)
  · exact Finset.mem_union_right _ (hReal (hcfg.2 h))
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := eraseMask_wires_subset G0 c.src c.bank h
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at w
    rcases w with rfl | w | w
    · exact hG0A
    · exact hSrcAllowed q w
    · exact hBankA q w

private theorem rename_wires_pad (f : Wire → Wire) {P Q : Program} (L : List Wire)
    (h : wires P ⊆ wires Q ∪ L.toFinset)
    (hf : ∀ x ∈ L, f x = x) :
    wires (renameProgram f P) ⊆ wires (renameProgram f Q) ∪ L.toFinset := by
  intro q hq
  rw [renameProgram_support, Finset.mem_image] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  rcases Finset.mem_union.mp (h hx) with hQ | hL
  · exact Finset.mem_union_left _ (by rw [renameProgram_support]; exact Finset.mem_image_of_mem f hQ)
  · rw [hf x (List.mem_toFinset.mp hL)]; exact Finset.mem_union_right _ hL

private theorem perm_fixes_allowed :
    (∀ x ∈ K0.core.pad.take 34, LowZero18Square.foldPerm K0 E0 x = x) ∧
    (∀ x ∈ K0.core.pad.take 34, R2SqEp760.sqSwap K0 E0 x = x) ∧
    (∀ q ∈ K0.core.pad.take 34, q ∈ allowedWires) ∧
    (∀ q ∈ cfgA.src, q ∈ allowedWires) ∧ (∀ q ∈ cfgB.src, q ∈ allowedWires) ∧ (∀ q ∈ cfgC.src, q ∈ allowedWires) ∧
    (∀ q ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), q ∈ allowedWires) ∧
    (∀ q ∈ ParkCopy.hosts E0, q ∈ allowedWires) ∧ (∀ q ∈ ParkCopyS.hostsS E0, q ∈ allowedWires) ∧
    LowZero18Square.cacheWire K0 cfgA.dst ∈ allowedWires ∧
    LowZero18Square.cacheWire K0 cfgB.dst ∈ allowedWires ∧
    LowZero18Square.cacheWire K0 cfgC.dst ∈ allowedWires := by
  have h1 : ∀ x ∈ K0.core.pad.take 34, StairSquareSites.LT48K.swF 4834 5093 x = x := by
    rw [K0_eq]; decide +kernel
  have h2 : ∀ x ∈ K0.core.pad.take 34, StairSquareSites.LT48K.swF 4875 5478 x = x := by
    rw [K0_eq]; decide +kernel
  have hAll : ∀ q ∈ K0.core.pad.take 34 ++ cfgA.src ++ cfgB.src ++ cfgC.src ++
      ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0) ++ ParkCopy.hosts E0 ++ ParkCopyS.hostsS E0 ++
      [LowZero18Square.cacheWire K0 cfgA.dst, LowZero18Square.cacheWire K0 cfgB.dst,
        LowZero18Square.cacheWire K0 cfgC.dst], q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by
        simp only [cfgA_fast, cfgB_fast, cfgC_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by
        simp only [cfgA_fast, cfgB_fast, cfgC_fast, K0_eq, E0_eq, hs_lit]; decide +kernel))
  refine ⟨fun x hx => by rw [StairSquareSites.LT48K.foldPerm_eq]; exact h1 x hx,
    fun x hx => by rw [StairSquareSites.LT48K.sqSwap_eq]; exact h2 x hx,
    fun q hq => hAll q (by simp [hq]), fun q hq => hAll q (by simp [hq]),
    fun q hq => hAll q (by simp [hq]), fun q hq => hAll q (by simp [hq]),
    fun q hq => hAll q (by simp [hq]), fun q hq => hAll q (by simp [hq]),
    fun q hq => hAll q (by simp [hq]),
    hAll _ (by simp), hAll _ (by simp), hAll _ (by simp)⟩

theorem brA_support : wires brA ⊆ wires (recBrA bodyAPlain) ∪ allowedWires.toFinset := by
  have pa := perm_fixes_allowed
  have hbase := withSplitPark_support_aux cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA
    pa.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.2.1
  have hbody : wires bodyA ⊆ wires bodyAPlain ∪ (K0.core.pad.take 34).toFinset := by
    intro q hq
    rcases Finset.mem_union.mp (bodyA_wires_plain hq) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_of_mem_take (by
        have : K0.core.pad.take 32 = (K0.core.pad.take 34).take 32 := by simp [List.take_take]
        rw [← this]; exact List.mem_toFinset.mp h)))
  have hB1 := rename_wires_pad (R2SqEp760.sqSwap K0 E0) (K0.core.pad.take 34) hbody pa.2.1
  have hB2 := rename_wires_pad (LowZero18Square.foldPerm K0 E0) (K0.core.pad.take 34) hB1 pa.1
  intro q hq
  rcases Finset.mem_union.mp (hbase hq) with h | h
  · rcases Finset.mem_union.mp (hB2 h) with hP | hA
    · refine Finset.mem_union_left _ ?_
      simp only [recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10, ParkCopy10.pB, R2SqEp760.bodySwap,
        wires_append, Finset.mem_union]
      left; left; left; left; right; exact hP
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (pa.2.2.1 q (List.mem_toFinset.mp hA)))
  · exact Finset.mem_union_right _ h

theorem brB_support : wires brB ⊆ wires (recBrB bodyB) ∪ allowedWires.toFinset := by
  have pa := perm_fixes_allowed
  have hbase := withSplitPark_support_aux cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB
    pa.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.2.2.1
  intro q hq
  rcases Finset.mem_union.mp (hbase hq) with h | h
  · refine Finset.mem_union_left _ ?_
    simp only [recBrB, ParkCopy.withLowK2P, ParkCopy.pB, R2SqEp760.bodySwap, wires_append, Finset.mem_union]
    left; left; left; left; right; exact h
  · exact Finset.mem_union_right _ h

theorem brC_support : wires brC ⊆ wires (recBrC bodyCPlain) ∪ allowedWires.toFinset := by
  have pa := perm_fixes_allowed
  have hbase := withSplitPark_support_aux cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC
    pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.2.2.2
  have hB1 := rename_wires_pad (R2SqEp760.sqSwap K0 E0) (K0.core.pad.take 34) bodyC_wires_plain pa.2.1
  have hB2 := rename_wires_pad (LowZero18Square.foldPerm K0 E0) (K0.core.pad.take 34) hB1 pa.1
  intro q hq
  simp only [brC, wires_append, Finset.mem_union] at hq
  rcases hq with (h | h) | h
  · refine Finset.mem_union_left _ ?_
    simp only [recBrC, SumSavedCBranch.branch, wires_append, Finset.mem_union]; left; left; exact h
  · rcases Finset.mem_union.mp (hbase h) with hb | ha
    · rcases Finset.mem_union.mp (hB2 hb) with hP | hA
      · refine Finset.mem_union_left _ ?_
        simp only [recBrC, SumSavedCBranch.branch, SumSavedPark.withLowK2S, ParkCopyS.pB, R2SqEp760.bodySwap,
          wires_append, Finset.mem_union]
        left; right; left; left; left; left; right; exact hP
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (pa.2.2.1 q (List.mem_toFinset.mp hA)))
    · exact Finset.mem_union_right _ ha
  · refine Finset.mem_union_left _ ?_
    simp only [recBrC, SumSavedCBranch.branch, wires_append, Finset.mem_union]; right; exact h

private theorem hs_not_allowed : ∀ q ∈ hs, q ∉ allowedWires := fun q hq ha => by
  rw [allowedWires, List.mem_filter] at ha
  have h := ha.2
  simp [hq] at h

private theorem hs_fix_perms : ∀ q ∈ hs, LowZero18Square.foldPerm K0 E0 q = q ∧ R2SqEp760.sqSwap K0 E0 q = q := by
  have h1 : ∀ q ∈ hs, StairSquareSites.LT48K.swF 4834 5093 q = q ∧ StairSquareSites.LT48K.swF 4875 5478 q = q := by rw [hs_lit]; decide +kernel
  intro q hq; rw [StairSquareSites.LT48K.foldPerm_eq, StairSquareSites.LT48K.sqSwap_eq]; exact h1 q hq

private theorem withSplitPark_avoids (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program) (hba : ∀ q ∈ hs, q ∉ wires body)
    (hSrcAllowed : ∀ q ∈ c.src, q ∈ allowedWires)
    (hParkAllowed : ∀ q ∈ parkHosts, q ∈ allowedWires)
    (hCacheAllowed : LowZero18Square.cacheWire K0 c.dst ∈ allowedWires) :
    ∀ q ∈ hs, q ∉ wires (withSplitPark c keepBits parkHosts body) := by
  have hsup := withSplitPark_support_aux c v keepBits parkHosts body hSrcAllowed hParkAllowed hCacheAllowed
  intro q hq hw
  rcases Finset.mem_union.mp (hsup hw) with hB | hA
  · rw [R2SqEp760.bodySwap, renameProgram_support, renameProgram_support, Finset.mem_image] at hB
    obtain ⟨y, hy, hyq⟩ := hB
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hfix := hs_fix_perms q hq
    have hx1 : R2SqEp760.sqSwap K0 E0 x = q := (LowZero18Square.foldPerm K0 E0).injective (hyq.trans hfix.1.symm)
    have hx2 : x = q := (R2SqEp760.sqSwap K0 E0).injective (hx1.trans hfix.2.symm)
    exact hba q hq (hx2 ▸ hx)
  · exact hs_not_allowed q hq (List.mem_toFinset.mp hA)

theorem brA_avoids : ∀ q ∈ hs, q ∉ wires brA :=
  withSplitPark_avoids cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA
    bodyA_avoids_hs perm_fixes_allowed.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.2.1

theorem brB_avoids : ∀ q ∈ hs, q ∉ wires brB :=
  withSplitPark_avoids cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB
    bodyB_avoids_hs perm_fixes_allowed.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.2.2.1

theorem brC_avoids : ∀ q ∈ hs, q ∉ wires brC := by
  have hmid := withSplitPark_avoids cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC
    bodyC_avoids_hs perm_fixes_allowed.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.2.2.2
  have sl := OwnDiagAll12Square.sum_lengths K0 hwK
  have hgp := addInPlace_wires (OwnDiagAll12Square.sumSrc K0) K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (by omega) (by omega)
  have hgc := subInPlace_wires (OwnDiagAll12Square.sumSrc K0) K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (by omega) (by omega)
  have hnot : ∀ q ∈ hs, q ∉ K0.core.cin :: ((OwnDiagAll12Square.sumSrc K0 ++ K0.core.sum) ++ OwnDiagAll12Square.sumBank K0) := by
    simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  intro q hq hw
  simp only [brC, wires_append, Finset.mem_union] at hw
  rcases hw with (h | h) | h
  · rw [OwnDiagAll12Square.gPrep, hgp, List.mem_toFinset] at h; exact hnot q hq h
  · exact hmid q hq h
  · rw [OwnDiagAll12Square.gClear, hgc, List.mem_toFinset] at h; exact hnot q hq h

end Branches

end ECDSAAdd.Entrant.PDSplitLeafSquare
end

-- ==== end PDSplitLeafSquare ====


/-! The concrete placed-wire receipt lives beside the split circuit, keeping the
caller admission proof light during standalone kernel replay. -/
namespace ECDSAAdd.Entrant.PDSplitLeafSquare
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

theorem allowedPlacedGood : allowedWires.all (fun w =>
    let q := StairPlaceFast.ugB (StairSquareSites.LT48K.placeF w)
    (Nat.ble q 513 || Nat.beq q 4112 || (Nat.ble 4115 q && Nat.blt q 4630) ||
      (Nat.ble 4886 q && Nat.blt q 5144) || (Nat.ble 5399 q && Nat.blt q 5656) || Nat.beq q 9814) &&
    !(Nat.beq q 5515 || Nat.beq q 5655 || Nat.beq q 5400 || Nat.beq q 5401)) = true := by
  rw [allowedWires_eq]
  decide +kernel

end ECDSAAdd.Entrant.PDSplitLeafSquare

/-! Closed integration receipts are shared here so Main replays their thin
applications rather than repeating the finite kernel evaluations. -/
namespace ECDSAAdd.Entrant.PDSplitLeafSquare.ReplayCertificates
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
  StairSquareHolesCore
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
private def tailE1B (q : Nat) : Nat :=
  StairPlaceFast.swB 1558 736 (StairPlaceFast.swB 1557 738 (StairPlaceFast.swB 1042 737
    (StairPlaceFast.swB 1813 527 (StairPlaceFast.swB 738 740 (StairPlaceFast.swB 737 739
      (StairPlaceFast.swB 527 741 q))))))

private def tailPmB (q : Nat) : Nat :=
  StairPlaceFast.pwB (StairPlaceFast.swB 785 1813 (tailE1B q) - 16)

def tailGood (q : Nat) : Bool :=
  (Nat.ble q 513 || Nat.beq q 4112 || (Nat.ble 4115 q && Nat.blt q 4630) ||
    (Nat.ble 4886 q && Nat.blt q 5144) || (Nat.ble 5399 q && Nat.blt q 5656) || Nat.beq q 9814) &&
  !(Nat.beq q 5515 || Nat.beq q 5655 || Nat.beq q 5400 || Nat.beq q 5401)
private def tailPrefix (x : Wire) := StairPlaceFast.swB 4840 4627 (tailPmB x)
private def tailSuffix (x : Wire) := StairPlaceFast.swB 4835 4373 (StairPlaceFast.swB 4836 4374
  (StairPlaceFast.swB 4837 4375 (StairPlaceFast.swB 4838 4376 (StairPlaceFast.swB 4839 4377 (tailPmB x)))))

theorem tailPrefixGood :
    ([base 2400, base 513, base 514] ++ E1Reflected.xR base ++ E1Reflected.srcR base ++ E1Reflected.cR base).all
    (fun x => tailGood (StairPlaceFast.ugB (tailPrefix x))) = true := by decide +kernel

theorem tailSuffixGood : (wireBlock base 0 258 ++ [base 513, base 514] ++ wireBlock base 770 515 ++ wireBlock base 1540 258 ++ [base 721, base 722, base 2400]).all
    (fun x => tailGood (StairPlaceFast.ugB (tailSuffix x))) = true := by decide +kernel

theorem archiveBank13 : (StairArchiveInactive.safe 13 false && StairArchiveInactive.safe 13 true) = true := by decide +kernel
theorem archiveBank10 : (StairArchiveInactive.safe 10 false && StairArchiveInactive.safe 10 true) = true := by decide +kernel

theorem transferAll {a b : List Wire} {f g : Wire → Bool}
    (cert : b.all g = true) (lists : a = b) (predicates : ∀ q, f q = g q) :
    a.all f = true := by
  rw [lists]
  exact (congrArg (fun h : Wire → Bool => b.all h) (funext predicates)).trans cert

theorem transferSites {P : Program} {f g : Wire → Bool}
    (cert : StairSiteAvoidance.allSites g P = true) (predicates : ∀ q, f q = g q) :
    StairSiteAvoidance.allSites f P = true :=
  (congrArg (fun h : Wire → Bool => StairSiteAvoidance.allSites h P) (funext predicates)).trans cert

end ECDSAAdd.Entrant.PDSplitLeafSquare.ReplayCertificates

namespace ECDSAAdd.Entrant.PDSplitLeafSquare.PhaseReceipts
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
  StairRestSupport StairConcreteAssembly DirectSkywalk OB5
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
abbrev phaseValid (q : Nat) := Stair44OuterSites.fit (StairPlaceFast.phasePlaceB q)
theorem clearSites : allSites phaseValid (skywalkArithmeticClear base) = true := by decide +kernel
theorem tickRSites : allSites phaseValid (renameProgram (sig 511) tickR) = true := by decide +kernel
theorem inverseSites : allSites phaseValid (renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)) = true := by decide +kernel
theorem mergedSites : allSites phaseValid (Six505.merged6) = true := by decide +kernel
theorem packSites : allSites phaseValid (Six505.packP false) = true := by decide +kernel
theorem afterSites : allSites phaseValid (ForwardSixPlacement.after false) = true := by decide +kernel
end ECDSAAdd.Entrant.PDSplitLeafSquare.PhaseReceipts
