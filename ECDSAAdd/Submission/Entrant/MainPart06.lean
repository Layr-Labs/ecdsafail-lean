import ECDSAAdd.Submission.Entrant.MainPart05

set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== IntegerTickRanges (ArthurOstapenko baaabf50, ported) =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TickRanges

def H : Nat := 2^255

theorem classify (x p i : Nat) (hx0 : 0<x) (hx : x<p) (hpodd : p%2=1)
    (hp : p<2^256) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
    z.u+z.v < H   ∨
    (z.v=p   ∧   z.u*2^i=x)   ∨
    (∃ t r : Nat, t+r=i   ∧   1  ≤  r   ∧   z.v*2^t=x   ∧   z.u*2^r+z.v=p   ∧   z.u+z.v<p) := by
  induction i with
  | zero =>
    exact Or.inr (Or.inl ⟨rfl,by simp [SkywalkNat.init]⟩)
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    generalize heq : SkywalkNat.step^[i] (SkywalkNat.init x p)=z at ih ⊢
    rcases ih with hs | hno | hone
    · exact Or.inl ((SkywalkNat.step_sum_nonincrease z).trans_lt hs)
    · obtain ⟨hv,hu⟩ := hno
      have hz : z.u  ≠  0 := by intro h; simp [h] at hu; omega
      have hul : z.u<p := by
        have hi : 1  ≤  2^i := Nat.one_le_two_pow
        nlinarith
      by_cases he : z.u%2=0
      · right; left
        refine ⟨by simp [SkywalkNat.step,hz,he,hv],?_⟩
        simp only [SkywalkNat.step,if_neg hz,if_pos he,pow_succ]
        have hh : z.u/2*2=z.u := by omega
        calc
          _ = (z.u/2*2)*2^i := by ring
          _ = x := by rw [hh,hu]
      · right; right
        have hodd : z.u%2=1 := by omega
        have hdiff : (p-z.u)/2*2=p-z.u := by omega
        refine ⟨i,1,by omega,by omega,?_,?_,?_⟩
        all_goals simp only [SkywalkNat.step,if_neg hz,if_neg he,hv,
          if_neg (show   ¬  p  ≤  z.u by omega)]
        · exact hu
        · norm_num; omega
        · omega
    · obtain ⟨t,r,htr,hr,hv,hu,hs⟩ := hone
      have vz : z.v  ≤  x := by
        have ht : 1  ≤  2^t := Nat.one_le_two_pow
        nlinarith
      have hz : z.u  ≠  0 := by intro h; simp [h] at hu; omega
      have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) (show 0<p from by omega) hpodd
      rw [heq] at valid
      have vo : z.v%2=1 := valid.2.1
      by_cases he : z.u%2=0
      · right; right
        refine ⟨t,r+1,by omega,by omega,?_,?_,?_⟩
        all_goals simp only [SkywalkNat.step,if_neg hz,if_pos he]
        · exact hv
        · rw [pow_succ]
          have hh : z.u/2*2=z.u := by omega
          calc
            _ = (z.u/2*2)*2^r+z.v := by ring
            _ = p := by rw [hh,hu]
        · omega
      · left
        unfold SkywalkNat.step
        rw [if_neg hz,if_neg he]
        have hpH : p<2*H := by simpa [H,pow_succ] using hp
        split_ifs <;> dsimp only <;> omega

theorem early_gap (x i : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (hi : 225  ≤  i   ∧   i  ≤  254) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)
    z.u+z.v < H   ∨   H  ≤  z.v := by
  have hp : ECDSAAdd.p<2^256 := by norm_num [ECDSAAdd.p]
  have hpodd : ECDSAAdd.p%2=1 := by norm_num [ECDSAAdd.p]
  have hpe : ECDSAAdd.p+(2^32+977)=2*H := by norm_num [ECDSAAdd.p,H]
  obtain hs | hno | hone := classify x ECDSAAdd.p i hx0 hx hpodd hp
  · exact Or.inl hs
  · exact Or.inr (by rw [hno.1]; norm_num [ECDSAAdd.p,H])
  · obtain ⟨t,r,htr,hr,hv,hu,_⟩ := hone
    by_cases ht : 2  ≤  t
    · by_cases hr2 : 2  ≤  r
      · left
        have tp : 4  ≤  2^t := by simpa using Nat.pow_le_pow_right (by decide : 1  ≤  (2:Nat)) ht
        have rp : 4  ≤  2^r := by simpa using Nat.pow_le_pow_right (by decide : 1  ≤  (2:Nat)) hr2
        have hsmall : 4*((SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).u+
            (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v)<2*ECDSAAdd.p := by nlinarith
        nlinarith
      · have re : r=1 := by omega
        have tt : 224  ≤  t := by omega
        have tp : 2^224  ≤  2^t := Nat.pow_le_pow_right (by decide) tt
        left
        rw [re] at hu
        norm_num at hu
        have vle : (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v<2^32 := by
          by_contra hh
          have vv : 2^32  ≤  (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v := by omega
          have mul := Nat.mul_le_mul vv tp
          norm_num at mul
          nlinarith
        nlinarith
    · have rr : 224  ≤  r := by omega
      have rle : r  ≤  254 := by omega
      have rp : 2^224  ≤  2^r := Nat.pow_le_pow_right (by decide) rr
      have rpbig : 2^32+977<2^r := by
        calc
          2^32+977 < 2^224 := by norm_num
          _   ≤   2^r := rp
      have ep : 2^(256-r)*2^r=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
      have exp : 256-r  ≤  32 := by omega
      have sm : 2^(256-r)  ≤  2^32 := Nat.pow_le_pow_right (by decide) exp
      let z := SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)
      change z.v*2^t=x at hv
      change z.u*2^r+z.v=ECDSAAdd.p at hu
      change z.u+z.v<H   ∨   H  ≤  z.v
      have ucap : z.u<2^32 := by
        have ub : z.u<2^(256-r) := by
          by_contra h
          have mm := Nat.mul_le_mul_right (2^r) (Nat.le_of_not_gt h)
          nlinarith
        omega
      by_cases vb : H  ≤  z.v
      · exact Or.inr vb
      · left
        by_contra ns
        have vl : z.v<H := by omega
        have vt : H<z.v+(2^32+977) := by omega
        have hm : 2^(255-r)*2^r=H := by
          rw [←pow_add]
          change 2^(255-r+r)=(2:Nat)^255
          congr 1
          omega
        have um : z.u<2^(255-r) := by
          by_contra hh
          have mm := Nat.mul_le_mul_right (2^r) (Nat.le_of_not_gt hh)
          nlinarith
        have mm := Nat.mul_le_mul_right (2^r) (show z.u+1  ≤  2^(255-r) by omega)
        nlinarith
end ECDSAAdd.Entrant.TickRanges
namespace ECDSAAdd.Entrant.TickRanges

def Outside (v : Int) : Prop := v< -(H:Int)  ∨  (H:Int) ≤ v

theorem encode_boundary (g s : Bool) (u v : Int) (hu : 0 ≤ u) (hv : 0<v)
    (hvo : v%2=1) (hb : u+v<2*(H:Int)) (gap : u+v<(H:Int)  ∨  (H:Int) ≤ v) :
    let r := SkywalkRails.encode g s u v
    let eo := SkywalkRails.route r.a r.b;
    - (H:Int)  ≤  (SkywalkRails.step r).h  ∧  (SkywalkRails.step r).h<(H:Int)  ∧
      (Outside eo.2 ↔ Outside (SkywalkRails.step r).k) := by
  have hp : 0<(H:Int) := by norm_num [H]
  have ucap : u<(H:Int) := by omega
  by_cases he : u%2=0
  · have step := SkywalkRails.step_encode_even g s u v hu hv hvo he
    have hl : (u+v)%2 ≠ 0 := by omega
    have hn : (-u)%2=0 := by omega
    have hneg : (-u)/2= -(u/2) := by omega
    cases g <;> cases s <;>
      simp only [SkywalkRails.encode,SkywalkRails.route,SkywalkRails.odd,
        SkywalkRails.signed,Bool.false_eq_true,if_false,if_true,hl,hn,he,
        ne_eq,not_false_eq_true,not_true_eq_false,decide_true,decide_false] at step ⊢ <;>
      rw [step] <;> dsimp only <;> unfold Outside <;> omega
  · have step := SkywalkRails.step_encode_odd g s u v hu hv hvo he
    have hl : (u+v)%2=0 := by omega
    have hn : (-u)%2 ≠ 0 := by omega
    cases g <;> cases s <;>
      simp only [SkywalkRails.encode,SkywalkRails.route,SkywalkRails.odd,
        SkywalkRails.signed,Bool.false_eq_true,if_false,if_true,hl,hn,he,
        ne_eq,not_false_eq_true,not_true_eq_false,decide_true,decide_false] at step ⊢ <;>
      rw [step] <;> dsimp only <;> unfold Outside <;> omega
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
theorem run_mid_congr (M X X' E : Program) (m : List Bool) (s : State)
    (hM : measurementCount M = 0) (hc : measurementCount X = measurementCount X')
    (h : ∀ r, run X r (run M [] s) = run X' r (run M [] s)) :
    run (M ++ X ++ E) m s = run (M ++ X' ++ E) m s := by
  rw [List.append_assoc, List.append_assoc, run_append M (X ++ E), run_append M (X' ++ E), hM,
    List.take_zero, List.drop_zero, run_append X E, run_append X' E, hc, h]

theorem run_zero_head (M R : Program) (m : List Bool) (s : State) (hM : measurementCount M = 0) :
    run (M ++ R) m s = run R m (run M [] s) := by
  rw [run_append, hM, List.take_zero, List.drop_zero]

theorem run_congr_head (X X' E : Program) (m : List Bool) (v : State)
    (hc : measurementCount X = measurementCount X') (h : ∀ r, run X r v = run X' r v) :
    run (X ++ E) m v = run (X' ++ E) m v := by
  rw [run_append, run_append X' E, hc, h]

theorem run_head_congr (P P' E : Program) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hP' : measurementCount P' = 0)
    (h : run P [] s = run P' [] s) :
    run (P ++ E) m s = run (P' ++ E) m s := by
  rw [run_append P E, run_append P' E, hP, hP', List.take_zero, List.drop_zero, h]

def addCopy : List Wire → List Wire → List Wire → Wire → Program
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, cin =>
      (if as = [] then [.CX cin c] else majority a b cin c) ++
        addCopy (a' :: as) (b' :: bs) cs c ++ eraseCarry a b cin c ++ [.CX a b, .CX cin b]
  | [a], [b], _, cin => [.CX a b, .CX cin b]
  | _, _, _, _ => []

theorem shape_two {x y carry : List Wire} (hy : y.length = 0 + 2) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) :
    ∃ a a' b b' c, x = [a, a'] ∧ y = [b, b'] ∧ carry = [c] := by
  rcases y with _ | ⟨b, _ | ⟨b', _ | ⟨b'', ys⟩⟩⟩ <;> simp at hy
  rcases x with _ | ⟨a, _ | ⟨a', _ | ⟨a'', xs⟩⟩⟩ <;> simp at hx
  rcases carry with _ | ⟨c, _ | ⟨c', cs⟩⟩ <;> simp at hc
  exact ⟨a, a', b, b', c, rfl, rfl, rfl⟩

theorem shape_succ {n : Nat} {x y carry : List Wire} (hy : y.length = n + 1 + 2)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    ∃ a a' a'' as b b' b'' bs c cs, x = a :: a' :: a'' :: as ∧ y = b :: b' :: b'' :: bs ∧
      carry = c :: cs := by
  rcases y with _ | ⟨b, _ | ⟨b', _ | ⟨b'', ys⟩⟩⟩ <;> simp at hy
  rcases x with _ | ⟨a, _ | ⟨a', _ | ⟨a'', xs⟩⟩⟩ <;> simp at hx
  rcases carry with _ | ⟨c, cs⟩ <;> simp at hc
  exact ⟨a, a', a'', xs, b, b', b'', ys, c, cs, rfl, rfl, rfl⟩

theorem regValue_nil' (st : BasisState) : regValue [] st = 0 := rfl

theorem addCopy_counts : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    toffoliCount (addCopy x y carry cin) = n ∧
    measurementCount (addCopy x y carry cin) = n + 1 := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    simp [addCopy, eraseCarry, toffoliCount, measurementCount]
  | succ n ih =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have h := ih (a' :: a'' :: as) (b' :: b'' :: bs) cs c (by simpa using hy)
        (by simpa using hx) (by simpa using hc)
    simp only [addCopy, List.cons_ne_nil, if_false, toffoliCount_append,
        measurementCount_append, h.1, h.2, majority, eraseCarry, toffoliCount, measurementCount]
    omega

theorem regValue_cons' (a : Wire) (r : List Wire) (st : BasisState) :
    regValue (a :: r) st = (st a).toNat + 2 * regValue r st := by
  cases h : st a <;> simp [regValue, h]

theorem copy_affine (A A' B B' C : Bool)
    (hX : A.toNat + 2*A'.toNat < 1 ∨ 3 ≤ A.toNat + 2*A'.toNat)
    (hS : (1 ≤ B.toNat+2*B'.toNat ∧ B.toNat+2*B'.toNat < 3) ↔
      (1 ≤ (A.toNat+2*A'.toNat+(B.toNat+2*B'.toNat)+C.toNat)%4 ∧
      (A.toNat+2*A'.toNat+(B.toNat+2*B'.toNat)+C.toNat)%4 < 3)) :
    carryBit A B C = C := by
  revert hX hS
  cases A <;> cases A' <;> cases B <;> cases B' <;> cases C <;> decide
theorem addCopy_eq : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    (cin :: (x ++ y ++ carry)).Nodup → ∀ (s : State) (m : List Bool),
    (∀ w ∈ carry, s.basis w = false) →
    (regValue x s.basis < 2^n ∨ 3 * 2^n ≤ regValue x s.basis) →
    ((2^n ≤ regValue y s.basis ∧ regValue y s.basis < 3*2^n) ↔
      (2^n ≤ (regValue x s.basis+regValue y s.basis+(s.basis cin).toNat)%2^(n+2) ∧
        (regValue x s.basis+regValue y s.basis+(s.basis cin).toNat)%2^(n+2) < 3*2^n)) →
    run (addCopy x y carry cin) m s = run (addInPlace x y carry cin) m s := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc hnd s m hclean hX hS
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have hbc : b ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hb'c : b' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hcc : cin ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hzero : s.basis c = false := hclean c (by simp)
    have hK : carryBit (s.basis a) (s.basis b) (s.basis cin) =
        (s.basis cin) := by
      apply copy_affine _ (s.basis a') _ _ _
      · simpa [regValue_cons', regValue_nil'] using hX
      · simpa [regValue_cons', regValue_nil'] using hS
    have hm1 : measurementCount ([.CX cin c] : Program) = 0 := rfl
    have hm2 : measurementCount (majority a b cin c) = 0 := rfl
    have hmid : run ([.CX cin c] : Program) [] s = run (majority a b cin c) [] s := by
      rw [majority_correct _ _ _ _ h4]
      simp only [run]
      apply State.extensionality
      · rfl
      · funext w
        simp only [writeBit, Function.update]
        by_cases hwc : w = c
        · subst hwc
          simp [hbc, hb'c, hcc, hzero, hK]
        · simp [hwc]
    simp only [addCopy, addInPlace, if_pos (rfl : ([] : List Wire) = []), List.append_assoc]
    exact run_head_congr _ _ _ m s hm1 hm2 hmid
  | succ n ih =>
    intro x y carry cin hy hx hc hnd s m hclean hX hS
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
    have hp1 : 2^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
    have hp3 : 2^(n+1+2) = 2 * 2^(n+2) := by rw [show n+1+2 = (n+2)+1 by omega, pow_succ]; ring
    rw [regValue_cons' a, regValue_cons' b] at hS
    rw [regValue_cons' a] at hX
    have step := sum_value_step A B C (regValue (a' :: a'' :: as) s.basis)
      (regValue (b' :: b'' :: bs) s.basis) (n+2)
    have hsb : (sumBit A B C).toNat ≤ 1 := by cases sumBit A B C <;> decide
    have hA : (s.basis a).toNat ≤ 1 := by cases s.basis a <;> decide
    have hX' : regValue (a' :: a'' :: as) s1.basis < 2^n ∨
        3 * 2^n ≤ regValue (a' :: a'' :: as) s1.basis := by
      rw [hxs]; omega
    have hB : (s.basis b).toNat ≤ 1 := by cases s.basis b <;> decide
    have hS' :
        (2^n ≤ regValue (b' :: b'' :: bs) s1.basis ∧
          regValue (b' :: b'' :: bs) s1.basis < 3*2^n) ↔
        (2^n ≤ (regValue (a' :: a'' :: as) s1.basis + regValue (b' :: b'' :: bs) s1.basis +
          (s1.basis c).toNat) % 2^(n+2) ∧
          (regValue (a' :: a'' :: as) s1.basis + regValue (b' :: b'' :: bs) s1.basis +
          (s1.basis c).toNat) % 2^(n+2) < 3*2^n) := by
      rw [hxs,hys,hc1]
      change (sumBit A B C).toNat + 2 * ((regValue (a' :: a'' :: as) s.basis +
        regValue (b' :: b'' :: bs) s.basis + (carryBit A B C).toNat) % 2^(n+2)) =
        ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
          (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+2+1) at step
      rw [show n+2+1 = n+1+2 by omega] at step
      generalize (regValue (a' :: a'' :: as) s.basis + regValue (b' :: b'' :: bs) s.basis +
        (carryBit A B C).toNat) % 2^(n+2) = S' at step ⊢
      generalize ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
        (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+1+2) = S at step hS
      omega
    have hmc : measurementCount (addCopy (a' :: a'' :: as) (b' :: b'' :: bs) cs c) =
        measurementCount (addInPlace (a' :: a'' :: as) (b' :: b'' :: bs) cs c) := by
      rw [(addCopy_counts n _ _ _ c (by simpa using hy) (by simpa using hx)
          (by simpa using hc)).2,
        (addInPlace_counts _ _ _ c (by simpa using hx) (by simpa using hc)).2]
      simp only [List.length_cons] at hy ⊢
      omega
    have hm0 : measurementCount (majority a b cin c) = 0 := rfl
    simp only [addCopy, addInPlace, List.cons_ne_nil, if_false]
    rw [List.append_assoc (majority a b cin c ++ _), List.append_assoc (majority a b cin c ++ _)]
    apply run_mid_congr _ _ _ _ m s hm0 hmc
    intro record
    rw [hfirst]
    exact ih _ _ _ c (by simpa using hy) (by simpa using hx) (by simpa using hc) hnd' s1 record
      hclean' hX' hS'

end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
def signedAddCopy (q : Wire) (x y carry : List Wire) : Program :=
  signComplement q x ++ addCopy x y carry q ++ signComplement q x

def Shape (n V : Nat) : Prop := V < 2^n ∨ 3*2^n ≤ V
def Band (n V : Nat) : Prop := 2^n ≤ V ∧ V<3*2^n

theorem shape_complement (n V : Nat) (hv : V < 2^(n+2)) (h : Shape n V) :
    Shape n (2^(n+2)-1-V) := by
  have pow : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  unfold Shape at *
  omega

theorem shape_of_signed (n V : Nat) (hv : V < 2^(n+2))
    (lo : -((2^n:Nat):Int) ≤ signedDecode (n+2) V)
    (hi : signedDecode (n+2) V < ((2^n:Nat):Int)) : Shape n V := by
  have p2 : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1) = 2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold signedDecode at lo hi
  split_ifs at lo hi <;> unfold Shape <;> omega

theorem signedAddCopy_eq (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (clean : ∀ w ∈ cs, s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Band n (regValue y s.basis) ↔ Band n (regValue y (run (signedAdd q x y cs) [] s).basis)) :
    run (signedAddCopy q x y cs) m s=run (signedAdd q x y cs) m s := by
  have hxnd : x.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1).1
  have qx : q∉x := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have dis : List.Disjoint x (y++cs) := by
    have h : (x++(y++cs)).Nodup := by simpa only [List.append_assoc] using (List.nodup_cons.mp hn).2
    exact (List.nodup_append'.mp h).2.2
  have zx := (signComplement_counts q x).2
  let u := run (signComplement q x) [] s
  have fan := signComplement_correct q x hxnd qx s []
  have ux : Shape n (regValue x u.basis) := by
    change Shape n (regValue x (run (signComplement q x) [] s).basis)
    rw [fan.2.2]
    cases hs : s.basis q
    · exact source
    · simpa only [hx,if_true] using shape_complement n _ (by simpa [hx] using regValue_lt x s.basis) source
  have clean' : ∀ w ∈ cs, u.basis w=false := by
    intro w hw
    exact (fan.2.1 w (fun h => List.disjoint_left.mp dis h (List.mem_append_right _ hw))).trans (clean w hw)
  have out (r : List Bool) :
      regValue y (run (signComplement q x) r (run (addInPlace x y cs q) r u)).basis =
      regValue y (run (addInPlace x y cs q) r u).basis := by
    have h := signComplement_correct q x hxnd qx (run (addInPlace x y cs q) r u) r
    apply regValue_congr
    intro w hw
    exact h.2.1 w (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw))
  have old : regValue y (run (signedAdd q x y cs) [] s).basis =
      regValue y (run (addInPlace x y cs q) [] u).basis := by
    simp only [signedAdd,List.append_assoc]
    rw [run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have add := addInPlace_correct x y cs q hn (hx.trans hy.symm) hc u [] clean'
  have uy : regValue y u.basis=regValue y s.basis := by
    exact regValue_congr _ _ _ (fun w hw => fan.2.1 w
      (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw)))
  have us : Band n (regValue y u.basis) ↔
      Band n ((regValue x u.basis+regValue y u.basis+(u.basis q).toNat)%2^(n+2)) := by
    rw [←uy,old,add.2.2,hy] at sum
    exact sum
  have eq (r : List Bool) := addCopy_eq n x y cs q hy (hx.trans hy.symm)
    hc hn u r clean' ux us
  simp only [signedAddCopy,signedAdd,List.append_assoc]
  rw [run_zero_head _ _ m s zx,run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq]
  have mc := addCopy_counts n x y cs q hy (hx.trans hy.symm) hc
  have mo := addInPlace_counts x y cs q (hx.trans hy.symm) hc
  rw [mc.2,mo.2,hy]
  rfl
def recordCopy (sx sy q : Wire) (x y cs : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedAddCopy q x y cs ++ skywalkSignToggle sx sy q

theorem signedAddCopy_counts (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length) :
    toffoliCount (signedAddCopy q x y cs)=n ∧ measurementCount (signedAddCopy q x y cs)=n+1 := by
  have h := addCopy_counts n x y cs q hy (hx.trans hy.symm) hc
  simp only [signedAddCopy,toffoliCount_append,measurementCount_append,
    (signComplement_counts q x).1,(signComplement_counts q x).2,h.1,h.2]
  exact ⟨by omega,by omega⟩

theorem toggle_frame (sx sy q : Wire) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (w : Wire) (hw : w≠q) :
    (run (skywalkSignToggle sx sy q) m s).basis w=s.basis w := by
  rw [skywalkSignToggle_correct sx sy q hqx hqy]
  simp [writeBit,hw]

theorem recordCopy_eq (n : Nat) (sx sy q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (clean : ∀w∈cs,s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Band n (regValue y s.basis) ↔ Band n (regValue y (run (signedRecord sx sy q x y cs) [] s).basis)) :
    run (recordCopy sx sy q x y cs) m s=run (signedRecord sx sy q x y cs) m s := by
  have qrest := (List.nodup_cons.mp hn).1
  have away (w : Wire) (hw : w∈x++y++cs) : w≠q := by
    intro he; subst w; exact qrest hw
  let u := run (skywalkSignToggle sx sy q) [] s
  have ut (w : Wire) (hw : w≠q) : u.basis w=s.basis w := toggle_frame sx sy q hqx hqy s [] w hw
  have ux : regValue x u.basis=regValue x s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  have uc : ∀w∈cs,u.basis w=false := by
    intro w hw
    exact (ut w (away w (by simp [hw]))).trans (clean w hw)
  have zx := (skywalkSignToggle_counts sx sy q).2
  have out (r : List Bool) :
      regValue y (run (skywalkSignToggle sx sy q) r (run (signedAdd q x y cs) r u)).basis =
      regValue y (run (signedAdd q x y cs) r u).basis :=
    regValue_congr _ _ _ (fun w hw => toggle_frame sx sy q hqx hqy _ r w (away w (by simp [hw])))
  have old : regValue y (run (signedRecord sx sy q x y cs) [] s).basis =
      regValue y (run (signedAdd q x y cs) [] u).basis := by
    simp only [signedRecord,List.append_assoc]
    rw [run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have uy : regValue y u.basis=regValue y s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  rw [←uy,old] at sum
  have eq (r : List Bool) := signedAddCopy_eq n q x y cs hx hy hc hn u r uc (ux ▸ source) sum
  have mc := (signedAddCopy_counts n q x y cs hx hy hc).2
  have mo := (signedWord_counts q x y cs (hx.trans hy.symm) hc).2.1
  simp only [recordCopy,signedRecord,List.append_assoc]
  rw [run_zero_head _ _ m s zx,run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq,mc,mo,hy]
  rfl
def narrowCopy (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  recordCopy L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1)) ++
    signComplement L.q (L.y.drop n)

theorem record_source (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0) :
    regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) m s).basis = regValue L.xp s.basis := by
  have h := signedRecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
    (signedRegValue L.xp s.basis) (signedRegValue L.yp s.basis) s m ⟨hq,rfl,rfl,clean⟩
  have eq := (signedRegValue_eq_iff L.xp _ _).mp h.2.2.1
  exact regValue_congr _ _ _ eq

theorem narrowCopy_eq (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) (s : State) (m : List Bool)
    (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0)
    (source : Shape n (regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis))
    (sum : Band n (regValue L.yp s.basis) ↔ Band n (regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis)) :
    run (narrowCopy L (n+2)) m s=run (narrowSignedRecord L (n+2)) m s := by
  have views := L.views (n+2) hw
  have clean' : ∀w∈L.carryLow,s.basis w=false := (regValue_zero _ _).mp clean
  have qx : L.sx≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have fan (r : List Wire) (hr : ∀w∈r,w∉L.yhigh) (v : State) (record : List Bool) :
      regValue r (run (signComplement L.q L.yhigh) record v).basis=regValue r v.basis := by
    have f := signComplement_correct L.q L.yhigh (L.high_nodup hn) (L.q_high hn) v record
    exact regValue_congr _ _ _ (fun w hw => f.2.1 w (hr w hw))
  have xaway : ∀w∈L.xp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp only [NarrowSignedRecordLayout.x,List.mem_append] at *; tauto)
  have yaway : ∀w∈L.yp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp [hw'])
  have outx : regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.xp xaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  have outy : regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.yp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.yp yaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  rw [outx,record_source L (n+2) hw hn s [] hq clean] at source
  rw [outy] at sum
  have eq (r : List Bool) := recordCopy_eq n L.sx L.sy L.q L.xp L.yp L.carryLow
    hw.x hw.y (hw.carry.trans hw.y.symm) (L.short_nodup hn) qx qy s r clean' source sum
  have mc := signedAddCopy_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have rz := (skywalkSignToggle_counts L.sx L.sy L.q).2
  have old := (signedWord_counts L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)).2.1
  have counts : measurementCount (recordCopy L.sx L.sy L.q L.xp L.yp L.carryLow)=
      measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) := by
    simp only [recordCopy,signedRecord,measurementCount_append,rz,mc.2,old,hw.y]
    omega
  simp only [narrowCopy,narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
  rw [run_append,run_append,run_take,run_take,eq,counts]
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic Baselines Challenge RecordedQuantum
theorem addCopy_wires (x y carry : List Wire) (cin : Wire) :
    wires (addCopy x y carry cin) ⊆ (cin :: (x ++ y ++ carry)).toFinset := by
  induction x generalizing y carry cin with
  | nil => simp [addCopy, wires]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [addCopy, wires]
      | cons b bs =>
        cases bs with
        | nil =>
          intro w hw
          simp only [addCopy, wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, Finset.notMem_empty, or_false] at hw
          simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
          tauto
        | cons b' bs => simp [addCopy, wires]
    | cons a' as =>
      cases y with
      | nil => simp [addCopy, wires]
      | cons b bs =>
        cases bs with
        | nil => simp [addCopy, wires]
        | cons b' bs =>
          cases carry with
          | nil => simp [addCopy, wires]
          | cons c cs =>
            have hr := ih (b' :: bs) cs c
            have hm : wires (majority a b cin c) = {a, b, cin, c} := by
              ext w; simp [majority, wires, Instr.wires]; tauto
            have he := eraseCarry_wires a b cin c
            intro w hw
            simp only [addCopy, wires_append, Finset.mem_union, he] at hw
            simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
            rcases hw with ((h | h) | h) | h
            · split_ifs at h
              · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
                  Finset.mem_singleton, Finset.notMem_empty, or_false] at h
                tauto
              · rw [hm] at h
                simp only [Finset.mem_insert, Finset.mem_singleton] at h
                tauto
            · have := hr h
              simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at this
              tauto
            · simp only [Finset.mem_insert, Finset.mem_singleton] at h
              tauto
            · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
                Finset.mem_singleton, Finset.notMem_empty, or_false] at h
              tauto

theorem addCopy_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: x ++ y ++ carry).Nodup) : GatePhysical (addCopy x y carry cin) := by
  induction x generalizing y carry cin with
  | nil => simp [addCopy, GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases y with
      | nil => simp [addCopy, GatePhysical]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [addCopy, GatePhysical]
        | nil =>
          have hab : a ≠ b := by
            intro e; subst b
            have h := List.nodup_iff_count.mp hn a
            simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h
            omega
          have hcb : cin ≠ b := by
            intro e; subst cin
            have h := List.nodup_iff_count.mp hn b
            simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h
            omega
          simp [addCopy, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hab, hcb]
    | cons a' xs =>
      cases y with
      | nil => simp [addCopy, GatePhysical]
      | cons b ys =>
        cases ys with
        | nil => simp [addCopy, GatePhysical]
        | cons b' ys =>
          cases carry with
          | nil => simp [addCopy, GatePhysical]
          | cons k ks =>
            have hs : [a,b,cin,k,b'].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons, List.count_append, List.count_nil] at h ⊢; omega
            have ht : (k :: (a'::xs) ++ (b'::ys) ++ ks).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons, List.count_append] at h ⊢; omega
            have hs4 : [a,b,cin,k].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hs q
              simp only [List.count_cons, List.count_nil] at h ⊢; omega
            have htail := ih (b'::ys) ks k ht
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
              not_or, not_false_eq_true, and_true] at hs
            rw [addCopy]
            simp only [gatePhysical_append]
            refine ⟨⟨⟨?_, htail⟩, eraseCarry_physical _ _ _ _⟩, ?_⟩
            · split_ifs
              · simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hs.2.1.2.1, hs.2.2.1.1,
                  Ne.symm hs.2.2.2]
              · exact majority_physical _ _ _ _ hs4
            · have hcb : cin ≠ b := Ne.symm hs.2.1.1
              simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hs.1.1, hcb]

theorem signedAddCopy_support (q : Wire) (x y cs : List Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    wires (signedAddCopy q x y cs) ⊆ wires (signedAdd q x y cs) := by
  rw [(signedWord_wires q x y cs hx hc).1]
  have fan : wires (signComplement q x) ⊆ (q::(x++y++cs)).toFinset := by
    intro w hw
    have h := signComplement_wires_subset q x hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  simp only [signedAddCopy,wires_append,Finset.union_subset_iff]
  exact ⟨⟨fan,addCopy_wires x y cs q⟩,fan⟩

theorem narrowCopy_counts (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    toffoliCount (narrowCopy L (n+2))+1=toffoliCount (narrowSignedRecord L (n+2)) ∧
      measurementCount (narrowCopy L (n+2))=measurementCount (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have h := signedAddCopy_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have old := narrowSignedRecord_counts L (n+2) hw
  have z := skywalkSignToggle_counts L.sx L.sy L.q
  have f := signComplement_counts L.q L.yhigh
  simp only [narrowCopy,recordCopy,v.1,v.2.1,v.2.2.1,v.2.2.2,
    toffoliCount_append,measurementCount_append,z.1,z.2,h.1,h.2,f.1,f.2,old.1,old.2.1]
  exact ⟨by omega,by omega⟩

theorem narrowCopy_support (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    wires (narrowCopy L (n+2)) ⊆ wires (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have sub := signedAddCopy_support L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  simp only [narrowCopy,narrowSignedRecord,recordCopy,signedRecord,v.1,v.2.1,v.2.2.1,v.2.2.2,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) sub)
    (Finset.Subset.refl _)) (Finset.Subset.refl _)

theorem signedAddCopy_physical (q : Wire) (x y cs : List Wire) (hn : (q::(x++y++cs)).Nodup) :
    GatePhysical (signedAddCopy q x y cs) := by
  have qx : q∉x := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
  have fan := signComplement_physical q x qx
  have top := addCopy_physical x y cs q hn
  simp only [signedAddCopy,gatePhysical_append]
  exact ⟨⟨fan,top⟩,fan⟩

theorem narrowCopy_physical (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) : GatePhysical (narrowCopy L (n+2)) := by
  have v := L.views (n+2) hw
  have nd := L.short_nodup hn
  have qx : L.sx≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have toggle : GatePhysical (skywalkSignToggle L.sx L.sy L.q) := by
    simp [skywalkSignToggle,GatePhysical,PhysicalInstr,ProperGate,qx,qy]
  have top := signedAddCopy_physical L.q L.xp L.yp L.carryLow nd
  have fan := signComplement_physical L.q L.yhigh (L.q_high hn)
  simp only [narrowCopy,recordCopy,v.1,v.2.1,v.2.2.1,v.2.2.2,gatePhysical_append]
  exact ⟨⟨⟨toggle,top⟩,toggle⟩,fan⟩

theorem top_slots_le_old (x y cs : List Wire) (c : Wire) :
    gateSlots (addCopy x y cs c) ≤ gateSlots (addInPlace x y cs c) := by
  induction x generalizing y cs c with
  | nil => simp [addCopy,addInPlace]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [addCopy,addInPlace]
      | cons b bs => cases bs <;> simp [addCopy,addInPlace]
    | cons a' as =>
      cases y with
      | nil => simp [addCopy,addInPlace]
      | cons b bs =>
        cases bs with
        | nil => simp [addCopy,addInPlace]
        | cons b' bs =>
          cases cs with
          | nil => simp [addCopy,addInPlace]
          | cons d ds =>
            have h := ih (b'::bs) ds d
            simp only [addCopy,addInPlace,gateSlots_append] at h ⊢
            split_ifs <;> simp only [majority_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots] at h ⊢ <;> omega

theorem narrowCopy_slots (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    gateSlots (narrowCopy L (n+2)) ≤ gateSlots (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have top := top_slots_le_old L.xp L.yp L.carryLow L.q
  simp only [narrowCopy,narrowSignedRecord,recordCopy,signedRecord,signedAddCopy,signedAdd,
    v.1,v.2.1,v.2.2.1,v.2.2.2,gateSlots_append]
  omega
end ECDSAAdd.Entrant.TickRanges
end

section
set_option exponentiation.threshold 512
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
def head (w : Nat → Wire) (i : Nat) : Program :=
  let L := W.compactSkywalkTickLayout w i
  (if i=224 ∨ (255 ≤ i  ∧  i ≤ 509) then W.repairedRoute L
    else skywalkRoute L.a0 L.b0 L.ah L.bh) ++ skywalkSignedHalf L.aSign L.ext

def tail (w : Nat → Wire) (i : Nat) : Program :=
  [.CX (W.compactSkywalkTickLayout w i).previous (W.compactSkywalkTickLayout w i).a0] ++
    W.compactSkywalkTickCleanup w i

def tick (w : Nat → Wire) (i : Nat) : Program :=
  if 225 ≤ i ∧ i ≤ 254 then
    head w i ++ narrowCopy (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
      (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i
  else TickGap.tick w i

theorem old_split (w : Nat → Wire) (i : Nat) (band : 225 ≤ i  ∧  i ≤ 254) :
    W.repairedTick w i = head w i ++
      narrowSignedRecord (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
        (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i := by
  have nf : ¬ W.fwdTrim i := by unfold W.fwdTrim; omega
  simp only [W.repairedTick,if_neg nf,W.repairedTick0,head,tail,W.compactSkywalkTick,narrowSkywalkTick]
  split_ifs  <;> simp only [List.append_assoc]

theorem repairedRoute_small_support (L : SkywalkIntegerLayout) (hv : L.Valid) (hpos : 0 < L.bMid.length) :
    wires (W.repairedRoute L) ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
  have lo := swapRegisters_wires L.a0 L.aMid L.bMid hv.mids
  have tm : L.bMid.getD (L.bMid.length-1) 0∈L.bMid := W.repair_member_getD _ _ (by omega)
  have ls : wires (swapRegisters L.a0 L.aMid L.bMid) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    have h := lo hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh] at h ⊢
    tauto
  have ss : wires (W.signRepair L.aSign L.bSign L.previous (L.bMid.getD (L.bMid.length-1) 0)) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [W.signRepair,wires,Instr.wires,correctionWires,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh,
      List.not_mem_nil,or_false]
    have ht : q=L.bMid.getD (L.bMid.length-1) 0 → q∈L.bMid := fun he => he ▸ tm
    tauto
  have cx : wires [.CX L.a0 L.b0] ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [W.repairedRoute,W.repairedSwap,wires_append,Finset.union_subset_iff]
  exact ⟨⟨ls,ss⟩,cx⟩

theorem head_aux (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).history::(W.compactSkywalkTickLayout w i).carry) :
    (run (head w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have hpos : 0 < L.bMid.length := by
    change 0 < (wireBlock w 771 (W.compactSkywalkTickPreWidth i-2)).length
    rw [wireBlock_length]
    have width := W.compactSkywalkTick_width_bounds i hi
    omega
  have dis : List.Disjoint (L.history::L.carry) (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)) := by
    have nd : ((L.history::L.carry)++(L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh))).Nodup := by
      apply List.nodup_iff_count.mpr
      intro a
      have h := List.nodup_iff_count.mp hv.nodup a
      simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at h ⊢
      omega
    exact (List.nodup_append'.mp nd).2.2
  have qaway : q∉L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh) := List.disjoint_left.mp dis hq
  have sup : wires (head w i) ⊆ (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    have inc : (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [List.mem_toFinset,List.mem_cons] at ha ⊢
      tauto
    have repair := (repairedRoute_small_support L hv hpos).trans inc
    have full : wires (skywalkRoute L.a0 L.b0 L.ah L.bh) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      have h := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      tauto
    have half : wires (skywalkSignedHalf L.aSign L.ext) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [skywalkSignedHalf,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,or_false] at ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,List.mem_singleton]
      tauto
    simp only [head,wires_append,Finset.union_subset_iff]
    split_ifs  <;> exact ⟨by assumption,half⟩
  exact run_preserves_outside _ _ _ _ (fun h => qaway (List.mem_toFinset.mp (sup h)))

theorem tail_prefix (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).half.take (W.compactSkywalkTickPostWidth i) ++
      (W.compactSkywalkTickLayout w i).b.take (W.compactSkywalkTickPostWidth i)) :
    (run (tail w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have words := W.compactSkywalkTick_words_disjoint w i hi hn
  have nd := (List.nodup_cons.mp (L.record_nodup hv)).2
  have wa : L.half.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).1
  have wb : L.b.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
  have adot : List.Disjoint (L.half.take n) (L.half.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wa
  have bdot : List.Disjoint (L.b.take n) (L.b.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wb
  have apart : q∉L.half.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact List.disjoint_left.mp adot hqa
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_drop h) (List.mem_of_mem_take hqb)
  have bpart : q∉L.b.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_take hqa) (List.mem_of_mem_drop h)
    · exact List.disjoint_left.mp bdot hqb
  have q0 : q≠L.a0 := by
    have qm : q∈L.half++L.b := by
      rcases List.mem_append.mp hq with hqa|hqb
      · exact List.mem_append_left _ (List.mem_of_mem_take hqa)
      · exact List.mem_append_right _ (List.mem_of_mem_take hqb)
    intro he
    subst q
    have h := List.nodup_iff_count.mp hv.nodup L.a0
    have hq' := List.count_pos_iff.mpr qm
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,List.count_nil,List.count_cons,List.count_append,
      List.count_singleton] at h hq'
    simp only [beq_self_eq_true,if_true] at h
    omega
  have valid := W.compactSkywalkTick_release_valid w i hi hn
  have af (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickARelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.1 v r).2.1 q apart
  have bf (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickBRelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.2 v r).2.1 q bpart
  simp only [tail,W.compactSkywalkTickCleanup,run_append,run_take]
  rw [bf,af]
  change Function.update s.basis L.a0 (s.basis L.a0 ^^ s.basis L.previous) q = s.basis q
  exact Function.update_of_ne q0 _ _
theorem route_aux_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈L.previous::L.history::L.ext::L.carry) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis q=s.basis q := by
  have hn : ((L.previous::L.history::L.ext::L.carry)++
      (L.a0::L.b0::(L.ah++L.bh))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hv.nodup w
    simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  apply run_preserves_outside
  intro hm
  have hh := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) hm
  exact List.disjoint_left.mp hd hq (List.mem_toFinset.mp hh)

theorem route_int_values (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (hp : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (hext : s.basis L.ext=false) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).phase=s.phase ∧
    signedRegValue (L.ext::L.ah) (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).1 ∧
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).2 ∧
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis L.a0=SkywalkRails.odd A := by
  have hna : L.ah≠[] := by simp [SkywalkIntegerLayout.ah]
  have hnb : L.bh≠[] := by simp [SkywalkIntegerLayout.bh]
  have hA := ha.symm.trans (signedRegValue_cons L.a0 L.ah s.basis hna)
  have hB := hb.symm.trans (signedRegValue_cons L.b0 L.bh s.basis hnb)
  have hpar : s.basis L.b0=(!s.basis L.a0) := by
    cases hca : s.basis L.a0 with
    | false =>
      cases hcb : s.basis L.b0 with
      | false =>
        simp [hca,hcb] at hA hB
        omega
      | true => rfl
    | true =>
      cases hcb : s.basis L.b0 with
      | false => rfl
      | true =>
        simp [hca,hcb] at hA hB
        omega
  have hctrl : s.basis L.a0=SkywalkRails.odd A := by
    cases hc : s.basis L.a0 with
    | false =>
      have he : A%2=0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
    | true =>
      have he : A%2≠0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  obtain ⟨hf,_,hctl,hlo,hrawA,hrawB⟩ := skywalkRoute_correct L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv) s m hpar
  have he0 : t.basis L.ext=false :=
    (route_aux_frame L hv s m L.ext (by simp)).trans hext
  have hsa : signedRegValue L.ah t.basis=
      if s.basis L.a0 then signedRegValue L.bh s.basis else signedRegValue L.ah s.basis := by
    have hh := congrArg (signedDecode L.ah.length) hrawA
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  have hsb : signedRegValue L.bh t.basis=
      if s.basis L.a0 then signedRegValue L.ah s.basis else signedRegValue L.bh s.basis := by
    have hh := congrArg (signedDecode L.bh.length) hrawB
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  refine ⟨hf,?_,?_,hctl.trans hctrl⟩
  · rw [signedRegValue_cons L.ext L.ah t.basis hna,he0,hsa]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega

  · change signedRegValue (L.b0::L.bh) t.basis=_
    rw [signedRegValue_cons L.b0 L.bh t.basis hnb,hlo,hsb]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega


theorem head_odd_value (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (par : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (he : s.basis L.ext=false) :
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh ++
      skywalkSignedHalf L.aSign L.ext) m s).basis=(SkywalkRails.route A B).2 := by
  have route := (route_int_values L hv A B par s [] ha hb he).2.2.1
  have zero := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh (L.high_lengths hv) (L.route_nodup hv)).2
  rw [run_append,zero,List.take_zero,List.drop_zero]
  have extaway (q : Wire) (hq : q∈L.b) : q≠L.ext := by
    intro hh
    subst q
    have cnt := List.nodup_iff_count.mp hv.nodup L.ext
    have mem := List.count_pos_iff.mpr hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.b,List.count_cons,List.count_append,
      List.count_nil,List.count_singleton,beq_self_eq_true,if_true] at cnt mem
    omega
  apply Eq.trans (show signedRegValue L.b _=signedRegValue L.b
      (run (skywalkRoute L.a0 L.b0 L.ah L.bh) [] s).basis from ?_) route
  unfold signedRegValue
  congr 1
  exact regValue_congr _ _ _ (fun q hq =>
    (skywalkSignedHalf_frame L.aSign L.ext _ m).2 q (extaway q hq))

theorem band_signed (n V : Nat) (hv : V<2^(n+2)) :
    Band n V ↔ signedDecode (n+2) V< -((2^n:Nat):Int) ∨
      ((2^n:Nat):Int)≤signedDecode (n+2) V := by
  have p2 : 2^(n+2)=4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1)=2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold Band signedDecode
  split_ifs <;> omega

theorem repaired_output_info (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat) (hx0 : 0<x) (hx : x<p) (cop : x.Coprime p)
    (band : 225 ≤ i ∧ i ≤ 254) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    Shape (n-2) (regValue (L.half.take n) (run (W.repairedTick w i) m s).basis) ∧
      (Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
        Band (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis)) := by
  dsimp only
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have hi : i<512 := by omega
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  have cap := W.iter_sum_late x p i hx0 hpo hp gap hx (by omega)
  have early := early_gap x i hx0 hx band
  obtain ⟨G,S,enc⟩ := SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at enc
  change r=SkywalkRails.encode G S (z.u:Int) (z.v:Int) at enc
  have u0 : 0 ≤ (z.u:Int) := by omega
  have v0 : 0 < (z.v:Int) := by exact_mod_cast valid.1
  have vo : (z.v:Int)%2=1 := by exact_mod_cast valid.2.1
  have cp : (z.u:Int)+(z.v:Int)<2*(H:Int) := by
    change z.u+z.v<2^256 at cap
    have : 2^256=2*H := by norm_num [H]
    exact_mod_cast (this ▸ cap)
  have eg : (z.u:Int)+(z.v:Int)<(H:Int) ∨ (H:Int) ≤ (z.v:Int) := by
    change z.u+z.v<H ∨ H≤z.v at early
    exact_mod_cast early
  have bounds := encode_boundary G S (z.u:Int) (z.v:Int) u0 v0 vo cp eg
  rw [←enc] at bounds
  have par : (r.a+r.b)%2=1 := by rw [enc]; exact SkywalkRails.encode_odd_sum G S _ _ vo
  have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp gap hx cop hi s hs
  have fit := W.narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp gap hx cop hi
  have out := W.compactSkywalkTickOutput_spec w i hi hn _ _ _ fit.1 fit.2.1 fit.2.2.1 fit.2.2.2.1 fit.2.2.2.2 s [] input
  have nw : n=257 := by unfold n W.compactSkywalkTickPostWidth W.narrowSkywalkWidth; omega
  have lenA : n ≤ L.half.length := by
    rw [W.compactSkywalkTick_half w i hi,wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i hi).2.2.1
  have lenB : L.b.length=n := by
    rw [W.compactSkywalkTick_b w i hi,wireBlock_length]
    unfold n W.compactSkywalkTickPostWidth W.compactSkywalkTickPreWidth
      W.narrowSkywalkRouteWidth W.narrowSkywalkWidth
    omega
  have av : (W.compactSkywalkTickARelease w i).retained=L.half.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenA
  have bv : (W.compactSkywalkTickBRelease w i).retained=L.b.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) (by change n ≤ L.b.length; omega)
  have a := out.2.1
  have b := out.2.2.1
  rw [av] at a
  rw [bv] at b
  have lenA' : (L.half.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenA]
  have lenB' : (L.b.take n).length=n := by simp [List.length_take,lenB]
  have old : run (W.repairedTick w i) m s=run (W.compactSkywalkTick w i) [] s :=
    W.repairedTick_eq w hn x p i hp0 hx0 hpo hp gap hx cop hi s m hs
  have valO : signedRegValue (L.b.take n) (run (head w i) m s).basis=
      (SkywalkRails.route r.a r.b).2 := by
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have he : ¬(i=224 ∨ (255 ≤ i ∧ i ≤ 509)) := by omega
    change signedRegValue _ (run _ m s).basis=_
    rw [head,if_neg he,List.take_of_length_le (by omega : L.b.length≤n)]
    exact head_odd_value L hv r.a r.b par s m input.1 input.2.1 input.2.2.2.1
  have rawShape : Shape (n-2) (regValue (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis) := by
    unfold signedRegValue at a
    rw [lenA'] at a
    rw [nw] at a ⊢
    apply shape_of_signed 255 _ (by have h := regValue_lt (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis; rw [lenA',nw] at h; exact h)
    · rw [a]; exact bounds.1
    · rw [a]; exact bounds.2.1
  refine ⟨old ▸ rawShape,?_⟩
  rw [old]
  have oy : Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
      Outside (SkywalkRails.route r.a r.b).2 := by
    have hh := band_signed 255 (regValue (L.b.take n) (run (head w i) m s).basis)
      (by have h := regValue_lt (L.b.take n) (run (head w i) m s).basis; rw [lenB',nw] at h; simpa only [nw] using h)
    unfold signedRegValue at valO
    rw [lenB',nw] at valO
    simpa only [nw,Nat.reduceSub,valO,Outside,H] using hh
  have ky : Band (n-2) (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis) ↔
      Outside (SkywalkRails.step r).k := by
    have hh := band_signed 255 (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
      (by have h := regValue_lt (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis; rw [lenB',nw] at h; simpa only [nw] using h)
    unfold signedRegValue at b
    rw [lenB',nw] at b
    simpa only [nw,Nat.reduceSub,b,Outside,H] using hh
  exact oy.trans (bounds.2.2.trans ky.symm)
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
theorem tick_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat) (hx0 : 0 < x) (hx : x < p) (cop : x.Coprime p) (hi : i < 512)
    (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (tick w i) m s=run (W.repairedTick w i) m s := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    let P := head w i
    let Q := narrowSignedRecord R n
    let E := tail w i
    let u := run P (m.take (measurementCount P)) s
    let v := run Q (m.drop (measurementCount P)) u
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have width := W.compactSkywalkTick_width_bounds i hi
    have npos : 2 ≤ n := width.2.1
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have nd : R.wires.Nodup := narrowSkywalkRecord_nodup L hv n (by omega) nlen
    have n2 : n-2+2=n := by omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have whole : run (W.repairedTick w i) m s=
        run E ((m.drop (measurementCount P)).drop (measurementCount Q)) v := by
      rw [old_split _ _ band,List.append_assoc,run_append,run_take,run_append,run_take]
      simp only [P,Q,E,u,v,run_take]
      rfl
    have sizes := repaired_output_info w hn x i hx0 hx cop band s m hs
    have keep (r : List Wire) (hr : r⊆L.half.take n++L.b.take n) :
        regValue r (run (W.repairedTick w i) m s).basis=regValue r v.basis := by
      rw [whole]
      apply regValue_congr
      intro q hq
      exact tail_prefix w i hi hn v _ q (hr hq)
    have shapeX : Shape (n-2) (regValue (L.half.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_left _ hq)]
      exact sizes.1
    have bandY : Band (n-2) (regValue (L.b.take n) u.basis) ↔
        Band (n-2) (regValue (L.b.take n) v.basis) := by
      have yu : run (head w i) m s=u := by dsimp only [u,P]; rw [run_take]
      have yv := keep (L.b.take n) (by intro q hq; exact List.mem_append_right _ hq)
      have sy : Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
          Band (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis) := sizes.2
      rw [yu,yv] at sy
      exact sy
    have record0 : (run Q [] u).basis=v.basis := run_basis_records Q u u [] (m.drop (measurementCount P)) rfl
    have orig := narrowSkywalkRecord_views L hv n (by omega) nlen
    have views := R.views n hw
    have xx : R.xp=L.half.take n := by rw [←views.1]; rw [orig.1]
    have yy : R.yp=L.b.take n := by rw [←views.2.1]; rw [orig.2.1]
    have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp gap hx cop hi s hs
    have uq : u.basis R.q=false := by
      apply (head_aux w i hi hn s _ L.history (List.mem_cons_self)).trans
      exact input.2.2.2.2.1
    have clean : regValue R.carryLow u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have qm : q∈L.carry := List.mem_of_mem_take hq
      apply (head_aux w i hi hn s _ q (List.mem_cons_of_mem _ qm)).trans
      exact (regValue_zero _ _).mp input.2.2.2.2.2 q qm
    have eq (r : List Bool) : run (narrowCopy R n) r u=run Q r u := by
      have a : Shape (n-2) (regValue R.xp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,xx,record0]
        exact shapeX
      have b : Band (n-2) (regValue R.yp u.basis) ↔
          Band (n-2) (regValue R.yp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,yy,record0]
        exact bandY
      simpa only [n2] using narrowCopy_eq (n-2) R hw' nd u r uq clean a b
    have counts : measurementCount (narrowCopy R n)=measurementCount Q := by
      simpa only [n2] using (narrowCopy_counts (n-2) R hw').2
    simp only [tick,if_pos band]
    rw [old_split _ _ band]
    change run ((P++narrowCopy R n)++E) m s=run ((P++Q)++E) m s
    conv_lhs => rw [List.append_assoc,run_append P (narrowCopy R n++E)]
    conv_rhs => rw [List.append_assoc,run_append P (Q++E)]
    change run (narrowCopy R n++E) (m.drop (measurementCount P)) u = run (Q++E) (m.drop (measurementCount P)) u
    rw [run_append (narrowCopy R n) E,run_append Q E]
    rw [run_take (narrowCopy R n),run_take Q,eq,counts]
  · simpa only [tick,if_neg band] using
      TickGap.tick_eq w hn x p i hp0 hx0 hpo hp (by norm_num [p]) hx cop hi s m hs

def due (i : Nat) : Nat := if 225 ≤ i ∧ i ≤ 254 then 1 else TickGap.due i

theorem tick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (tick w i)+due i=toffoliCount (W.repairedTick w i)  ∧
    measurementCount (tick w i)=measurementCount (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_counts (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,due,if_pos band,toffoliCount_append,measurementCount_append]
    exact ⟨by omega,by omega⟩
  · simpa only [tick,if_neg band,due,if_neg band] using TickGap.tick_counts w i hi hn

theorem tick_support (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    wires (tick w i) ⊆ wires (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_support (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)
  · simpa only [tick,if_neg band] using TickGap.tick_support w i hi hn

theorem tick_slots (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    Challenge.gateSlots (tick w i)  ≤  Challenge.gateSlots (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_slots (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,Challenge.gateSlots_append]
    omega
  · simpa only [tick,if_neg band] using TickGap.tick_slots w i hi hn

theorem tick_physical (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (tick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_physical (n-2) R hw' (narrowSkywalkRecord_nodup L hv n (by omega) nlen)
    simp only [n2] at h
    dsimp only [R,n,L] at h
    have old := W.repairedTick_physical w i hi hn
    rw [old_split _ _ band] at old
    simp only [tick,if_pos band,gatePhysical_append] at old ⊢
    exact ⟨⟨old.1.1,h⟩,old.2⟩
  · simpa only [tick,if_neg band] using TickGap.tick_physical w i hi hn
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic MappedCompressed Secp256k1 History5 OB5

theorem tick_eq5 (x : Nat) (hx0 : 0 < x) (hx : x < p) (i : Nat) (hi : i < 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (tick base i) m s=run (W.repairedTick base i) m s := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  have dis := Stack5.prefix_disjoint_layout base base_pool_nodup i i (Nat.le_refl i) hi
  have read : ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,s.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    exact run_preserves_outside _ _ _ q (fun he => Finset.disjoint_left.mp dis he hq)
  have old := W.repairedTick_support base i hi base_pool_nodup
  have fresh := (tick_support base i hi base_pool_nodup).trans old
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 < 2^256 := by norm_num [p]
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (tick_eq base base_pool_nodup x i hx0 hx cop hi raw m hraw)

theorem block_eq (x : Nat) (hx0 : 0 < x) (hx : x < p) (i : Nat) (hi : i < 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (tick base i++FirstNonzeroCodec.pack8first base i) m s=run (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) m s := by
  rw [run_append (tick base i),run_append (W.repairedTick base i),run_take (tick base i),run_take (W.repairedTick base i)]
  rw [tick_eq5 x hx0 hx i hi s m hs,(tick_counts base i hi base_pool_nodup).2]

def forward (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)++forward (i+1) n

/-- The replacement forward prefix has exactly the existing logical trajectory. -/
theorem forward_gen (x : Nat) (hx0 : 0 < x) (hx : x < p) (n : Nat) :
    ∀ i, 1 ≤ i → i+n ≤ 512 → ∀(s : State)(m : List Bool),
    W.CompressedCompactStage5 base x p i s.basis →
    run (forward i n) m (pullState (sig (i-1)) s)=
      pullState (sig (i+n-1)) (run (Stack5.forward5 base i n) m s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  induction n with
  | zero => intro i _ _ s m _; simp only [forward,Stack5.forward5,run,Nat.add_zero]
  | succ n ih =>
    intro i h1 hb s m hs
    have hi : i ≤ 511 := by omega
    have z := StackOB5.stage_zero x i (by omega) s.basis hs
    rw [pull_step i hi s z.1 z.2]
    have cnt : measurementCount (renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i))=
        measurementCount (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) := by
      rw [(renameProgram_counts (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)).2]
      simp only [measurementCount_append,(tick_counts base i (by omega) base_pool_nodup).2]
    rw [forward,Stack5.forward5,run_append _ (forward (i+1) n),run_append _ (Stack5.forward5 base (i+1) n),cnt,StackOB5.forward_step_records,OB5.run_rename i hi]
    rw [block_eq x hx0 hx i (by omega) s _ hs]
    rw [StackOB5.forward_step_eq base base_pool_nodup x p i hp0 hx0 hpo hp hpGap hx cop _ _ hs]
    have next := (Stack5.step_spec base base_pool_nodup StackOB5.historyAbove x p i hp0 hx0 hpo hp hpGap hx
      cop (by omega) s (m.take (measurementCount (W.repairedTick base i++History5.packAfter base i))) hs).2
    have step := ih (i+1) (by omega) (by omega) _ (m.drop (measurementCount (W.repairedTick base i++History5.packAfter base i))) next
    rw [show i+1-1=i by omega] at step
    rw [step,show i+1+n-1=i+(n+1)-1 by omega]

theorem forward_eq (x : Nat) (hx0 : 0 < x) (hx : x < p) (i n : Nat) (h1 : 1 ≤ i) (hi : i+n ≤ 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (forward i n) m (pullState (sig (i-1)) s)=run (StackOB5.forward i n) m (pullState (sig (i-1)) s) := by
  rw [forward_gen x hx0 hx n i h1 hi s m hs,StackOB5.forward_gen x hx0 hx n i h1 hi s m hs]

def count (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => due i+count (i+1) n

theorem forward_metrics (i n : Nat) (hi : i+n ≤ 512) :
    toffoliCount (forward i n)+count i n=toffoliCount (StackOB5.forward i n)  ∧
    measurementCount (forward i n)=measurementCount (StackOB5.forward i n)  ∧
    Challenge.gateSlots (forward i n) ≤ Challenge.gateSlots (StackOB5.forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,StackOB5.forward,count]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have stepCounts := tick_counts base i (by omega) base_pool_nodup
    have slots := tick_slots base i (by omega) base_pool_nodup
    have a := renameProgram_counts (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)
    have b := renameProgram_counts (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    have c := Baselines.rename_gateSlots (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)
    have d := Baselines.rename_gateSlots (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    simp only [forward,StackOB5.forward,count,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at a b c d ⊢
    exact ⟨by omega,by omega,by omega⟩

theorem forward_support (i n : Nat) (hi : i+n ≤ 512) : wires (forward i n)⊆wires (StackOB5.forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,StackOB5.forward]
  | succ n ih =>
    have fresh := tick_support base i (by omega) base_pool_nodup
    have block : wires (tick base i++FirstNonzeroCodec.pack8first base i) ⊆ wires (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) := by
      simp only [wires_append]
      exact Finset.union_subset_union fresh (Finset.Subset.refl _)
    have ren : wires (renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)) ⊆
        wires (renameProgram (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)) := by
      rw [renameProgram_support,renameProgram_support]
      exact Finset.image_mono (sig i) block
    simp only [forward,StackOB5.forward,wires_append]
    exact Finset.union_subset_union ren (ih (i+1) (by omega))

theorem forward_physical (i n : Nat) (hi : i+n ≤ 512) : GatePhysical (forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have stepPhysical := tick_physical base i (by omega) base_pool_nodup
    have codec := (FirstNonzeroCodec.packet_physical base base_pool_nodup i (by omega)).1
    have ren := gatePhysical_rename (sig i) (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr ⟨stepPhysical,codec⟩)
    simp only [forward,gatePhysical_append]
    exact ⟨ren,ih (i+1) (by omega)⟩

theorem count_508 : count 1 508=62 := by decide +kernel
end ECDSAAdd.Entrant.TickRanges
end

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588TickGapWalk =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.TickGap1591Arithmetic
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Integer

/-! Forward TickGap on the checked A/B integer stage. The packet programs,
the three terminal ticks, and the complete reverse walk stay unchanged. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed Secp256k1 OB5
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

theorem tick_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i : Nat) (hi : i<512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (TickRanges.tick base i) m s=run (W.repairedTick base i) m s := by
  obtain ⟨raw,oldStage,read⟩ := Rolling1588.Integer.old_stage_local
    base isA base_pool_nodup x p i hi s stage
  have old := W.repairedTick_support base i hi base_pool_nodup
  have fresh := (TickRanges.tick_support base i hi base_pool_nodup).trans old
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (TickRanges.tick_eq5 x hx0 hx i hi raw m oldStage)

theorem block_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i : Nat) (hi : i<512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i) m s=
      run (W.repairedTick base i++Rolling1588.Integer.packFirst base isA i) m s := by
  rw [run_append (TickRanges.tick base i),run_append (W.repairedTick base i),
    run_take (TickRanges.tick base i),run_take (W.repairedTick base i),
    tick_run_eq isA x hx0 hx i hi s m stage,
    (TickRanges.tick_counts base i hi base_pool_nodup).2]

def forward (isA : Bool) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (sig i)
      (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)++
        forward isA (i+1) n

def count (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => TickRanges.due i+count (i+1) n

def stackForward (isA : Bool) : Program :=
  forward isA 1 508 ++
    renameProgram (sig 510) (tickMF++Rolling1588.packAtTick isA 510) ++
    renameProgram (sig 511) tickF

attribute [local irreducible] forward stackForward Rolling1588.forward
  Rolling1588.Integer.forward Rolling1588.stackForward

theorem forward_gen (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (n : Nat) :
    ∀i,1 ≤ i → i+n ≤ 512 → ∀(s : State)(m : List Bool),
      Rolling1588.Integer.Stage base isA x p i s.basis →
      run (forward isA i n) m (pullState (sig (i-1)) s)=
        pullState (sig (i+n-1)) (run (Rolling1588.Integer.regularForward base isA i n) m s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  induction n with
  | zero =>
    intro i _ _ s m _
    simp only [forward,Rolling1588.Integer.regularForward,run,Nat.add_zero]
  | succ n ih =>
    intro i h1 bound s m stage
    have hi : i ≤ 511 := by omega
    have zero := Rolling1588.Integer.stage_zero isA x i (by omega) s.basis stage
    rw [pull_step i hi s zero.1 zero.2]
    have mapped := (renameProgram_counts (sig i)
      (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)).2
    have records :
        measurementCount (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)=
          measurementCount (W.repairedTick base i++Rolling1588.Integer.packAfter base isA i) := by
      rw [measurementCount_append,measurementCount_append,
        (TickRanges.tick_counts base i (by omega) base_pool_nodup).2,
        Rolling1588.Integer.packFirst_records]
    rw [forward,Rolling1588.Integer.regularForward,run_append,run_append,mapped,records,
      OB5.run_rename i hi,block_run_eq isA x hx0 hx i (by omega) s _ stage,
      Rolling1588.Integer.forward_step_eq base isA base_pool_nodup x p i
        hp0 hx0 hpo hp gap hx cop _ _ stage]
    have next := (Rolling1588.Integer.step_spec base isA base_pool_nodup
      StackOB5.historyAbove x p i hp0 hx0 hpo hp gap hx cop (by omega) s
        (m.take (measurementCount (W.repairedTick base i++
          Rolling1588.Integer.packAfter base isA i))) stage).2
    have rest := ih (i+1) (by omega) (by omega) _
      (m.drop (measurementCount (W.repairedTick base i++
        Rolling1588.Integer.packAfter base isA i))) next
    rw [show i+1-1=i by omega,show i+1+n-1=i+(n+1)-1 by omega] at rest
    exact rest

theorem forward_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i n : Nat) (h1 : 1 ≤ i) (bound : i+n ≤ 512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (forward isA i n) m (pullState (sig (i-1)) s)=
      run (Rolling1588.forward isA i n) m (pullState (sig (i-1)) s) := by
  rw [←Rolling1588.Integer.forward_eq_packets]
  rw [forward_gen isA x hx0 hx n i h1 bound s m stage,
    Rolling1588.Integer.forward_gen isA x hx0 hx n i h1 bound s m stage]

theorem forward_first_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (n : Nat) (bound : 1+n ≤ 512) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (forward isA 1 n) m s=run (Rolling1588.forward isA 1 n) m s := by
  have same := forward_run_eq isA x hx0 hx 1 n (Nat.le_refl 1) bound s m
    (Rolling1588.Integer.stage_one base isA x p s first)
  have start : pullState (sig (1-1)) s=s := by
    apply State.extensionality
    · rfl
    · funext q
      change s.basis (sig 0 q)=s.basis q
      rw [sig_zero]
  rwa [start] at same

private theorem forward_integer_metrics (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    toffoliCount (forward isA i n)+count i n=
        toffoliCount (Rolling1588.Integer.forward isA i n) ∧
      measurementCount (forward isA i n)=measurementCount (Rolling1588.Integer.forward isA i n) ∧
      Challenge.gateSlots (forward isA i n) ≤
        Challenge.gateSlots (Rolling1588.Integer.forward isA i n) := by
  induction n generalizing i with
  | zero =>
    simp [forward,Rolling1588.Integer.forward,count,toffoliCount,measurementCount,Challenge.gateSlots]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have step := TickRanges.tick_counts base i (by omega) base_pool_nodup
    have slots := TickRanges.tick_slots base i (by omega) base_pool_nodup
    simp only [forward,Rolling1588.Integer.forward,count,toffoliCount_append,
      measurementCount_append,Challenge.gateSlots_append,
      (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
      Baselines.rename_gateSlots]
    exact ⟨by omega,by omega,by omega⟩

theorem forward_metrics (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    toffoliCount (forward isA i n)+count i n=toffoliCount (Rolling1588.forward isA i n) ∧
      measurementCount (forward isA i n)=measurementCount (Rolling1588.forward isA i n) ∧
      Challenge.gateSlots (forward isA i n) ≤ Challenge.gateSlots (Rolling1588.forward isA i n) := by
  simpa only [Rolling1588.Integer.forward_eq_packets] using
    forward_integer_metrics isA i n bound

theorem count_508 : count 1 508=62 := by decide +kernel

theorem stackForward_metrics (isA : Bool) :
    toffoliCount (stackForward isA)+62=toffoliCount (Rolling1588.stackForward isA) ∧
      measurementCount (stackForward isA)=measurementCount (Rolling1588.stackForward isA) ∧
      Challenge.gateSlots (stackForward isA) ≤ Challenge.gateSlots (Rolling1588.stackForward isA) := by
  have head := forward_metrics isA 1 508 (by omega)
  rw [count_508] at head
  simp only [stackForward,Rolling1588.stackForward,toffoliCount_append,
    measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem forward_integer_support (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    wires (forward isA i n)⊆wires (Rolling1588.Integer.forward isA i n) := by
  induction n generalizing i with
  | zero => simp [forward,Rolling1588.Integer.forward,wires]
  | succ n ih =>
    have block : wires (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)⊆
        wires (W.repairedTick base i++Rolling1588.Integer.packFirst base isA i) := by
      rw [wires_append,wires_append]
      exact Finset.union_subset_union
        (TickRanges.tick_support base i (by omega) base_pool_nodup) (Finset.Subset.refl _)
    have placed := Finset.image_mono (sig i) block
    rw [←renameProgram_support,←renameProgram_support] at placed
    simp only [forward,Rolling1588.Integer.forward,wires_append]
    exact Finset.union_subset_union placed (ih (i+1) (by omega))

theorem forward_support (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    wires (forward isA i n)⊆wires (Rolling1588.forward isA i n) := by
  simpa only [Rolling1588.Integer.forward_eq_packets] using
    forward_integer_support isA i n bound

theorem stackForward_support (isA : Bool) :
    wires (stackForward isA)⊆wires (Rolling1588.stackForward isA) := by
  simp only [stackForward,Rolling1588.stackForward,wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (forward_support isA 1 508 (by omega)) (Finset.Subset.refl _))
      (Finset.Subset.refl _)

private theorem append_run_eq (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem stackForward_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward isA) m s=run (Rolling1588.stackForward isA) m s := by
  have same := append_run_eq (forward isA 1 508) (Rolling1588.forward isA 1 508)
    (renameProgram (sig 510) (tickMF++Rolling1588.packAtTick isA 510) ++
      renameProgram (sig 511) tickF) s m
    (forward_metrics isA 1 508 (by omega)).2.1
    (fun r=>forward_first_run_eq isA x hx0 hx 508 (by omega) s r first)
  simpa only [stackForward,Rolling1588.stackForward,List.append_assoc] using same

theorem stackForward_boundary (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward isA) m s=pullState (sig 511)
      (run (Rolling1588.allEncode base isA 102) []
        (run (W.compactSkywalkForward base 1 511) [] s)) := by
  rw [stackForward_run_eq isA x hx0 hx s m first]
  exact Rolling1588.stackForward_boundary isA hn hlo x hx0 hx s m first

theorem stack_roundtrip (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (Rolling1588.stackReverse isA) mD (run (stackForward isA) mE s)=s := by
  rw [stackForward_run_eq isA x hx0 hx s mE first]
  exact Rolling1588.stack_roundtrip isA hn hlo x hx0 hx s mE mD first

end ECDSAAdd.Entrant.Rolling1588TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588TickGapPhases =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588TickGapWalk
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Native
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Kernel
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588KernelResources

/-! The new forward phase has the exact old A/B State boundary. All native,
field, inverse, host, and caller interfaces are retained. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Challenge Baselines
  FrontierEntry1591Callers OB5
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  forward stackForward Rolling1588.forward Rolling1588.stackForward Rolling1588.stackReverse
  FrontierEntry1591Native.forward FrontierEntry1591Native.inverse
  Rolling1588.firstPhase Rolling1588.lastPhase

def tailPhase (isA : Bool) : Program := stackForward isA++skywalkArithmeticClear base

def firstPhase (isA : Bool) : Program := FrontierEntry1591Native.forward base++tailPhase isA

def oldKernel (a b : Bool) (F : Program) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a)++
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b))

def kernel (a b : Bool) (F : Program) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (firstPhase a)++
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b))

def entryKernel : Program := kernel true false Rolling1588.entryFieldHosted
def exitKernel : Program := kernel false true Rolling1588.exitFieldHosted

attribute [local irreducible] tailPhase firstPhase oldKernel kernel entryKernel exitKernel
  Rolling1588.entryKernel Rolling1588.exitKernel

private theorem first_run_eq_of_stack (N F F0 C : Program) (s : State) (m : List Bool)
    (records : measurementCount F=measurementCount F0)
    (same : ∀mn mf,run F mf (run N mn s)=run F0 mf (run N mn s)) :
    run (N++(F++C)) m s=run (N++(F0++C)) m s := by
  simp only [run_append,records]
  rw [same]

theorem first_run_eq (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (firstPhase isA) m s=run (Rolling1588.firstPhase isA) m s := by
  have same (mn mf : List Bool) :
      run (stackForward isA) mf (run (FrontierEntry1591Native.forward base) mn s)=
        run (Rolling1588.stackForward isA) mf
          (run (FrontierEntry1591Native.forward base) mn s) :=
    stackForward_run_eq isA x hx0 hx _ mf
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [firstPhase,tailPhase,Rolling1588.firstPhase,List.append_assoc] using
    first_run_eq_of_stack (FrontierEntry1591Native.forward base) (stackForward isA)
      (Rolling1588.stackForward isA) (skywalkArithmeticClear base) s m
      (stackForward_metrics isA).2.1 same

private theorem state_fact_of_eq (P : State→Prop) (a b : State)
    (same : a=b) (fact : P b) : P a := by
  cases same
  exact fact

theorem first_clean (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    ∀q∈FrontierEntry1591Native.workSites,(run (firstPhase isA) m s).basis q=false := by
  exact state_fact_of_eq
    (fun t=>∀q∈FrontierEntry1591Native.workSites,t.basis q=false)
    (run (firstPhase isA) m s) (run (Rolling1588Lifetime.firstPhase isA) m s)
    (first_run_eq isA hn x y hx0 hx s m input)
    (Rolling1588Lifetime.first_clean isA hn hlo x y hx0 hx s m input)

theorem first_phase (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    (run (firstPhase isA) m s).phase=s.phase := by
  exact state_fact_of_eq (fun t=>t.phase=s.phase)
    (run (firstPhase isA) m s) (run (Rolling1588Lifetime.firstPhase isA) m s)
    (first_run_eq isA hn x y hx0 hx s m input)
    (Rolling1588Lifetime.first_phase isA hn hlo x y hx0 hx s m input)

theorem first_boundary (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (firstPhase isA) m s=pullState (sig 511)
      (run (Rolling1588.allEncode base isA 102) []
        (run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) []
          (run (FrontierEntry1591Native.forward base)
            (m.take (measurementCount (FrontierEntry1591Native.forward base))) s)))) := by
  rw [first_run_eq isA hn x y hx0 hx s m input]
  exact Rolling1588Lifetime.first_boundary isA hn hlo x y hx0 hx s m input

theorem phases_roundtrip (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (mE mD : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (Rolling1588.lastPhase isA) mD (run (firstPhase isA) mE s)=s := by
  rw [first_run_eq isA hn x y hx0 hx s mE input]
  exact Rolling1588Lifetime.phases_roundtrip isA hn hlo x y hx0 hx s mE mD input

theorem first_metrics (isA : Bool) :
    toffoliCount (firstPhase isA)+62=toffoliCount (Rolling1588.firstPhase isA) ∧
      measurementCount (firstPhase isA)=measurementCount (Rolling1588.firstPhase isA) ∧
      gateSlots (firstPhase isA) ≤ gateSlots (Rolling1588.firstPhase isA) := by
  have stack := stackForward_metrics isA
  simp only [firstPhase,tailPhase,Rolling1588.firstPhase,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem first_support (isA : Bool) :
    wires (firstPhase isA)⊆wires (Rolling1588.firstPhase isA) := by
  simp only [firstPhase,tailPhase,Rolling1588.firstPhase,wires_append,Finset.union_assoc]
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (stackForward_support isA) (Finset.Subset.refl _))

private theorem mapped_code_physical (isA : Bool) (f : Fin 10→Wire)
    (hf : Function.Injective f) :
    GatePhysical (renameProgram (MeasuredCodec5.label f) (Rolling1588.codeEncode isA)) := by
  have support : wires (Rolling1588.codeEncode isA)⊆Finset.range 10 := by
    simpa only [(Rolling1588.code_support isA).1] using
      (Finset.Subset.refl (Finset.range 10))
  exact gatePhysical_rename_support _ _
    (fun a ha b hb eq=>FirstNonzeroCodec.label_inj' f hf a (support ha) b (support hb) eq)
    (Rolling1588.code_physical isA).1

private theorem pack_physical (isA : Bool) (i : Nat) (hi : i<512) :
    GatePhysical (Rolling1588.packAtTick isA i) := by
  by_cases first : i=5
  · simp only [Rolling1588.packAtTick,if_pos first]
    exact (ParityCodec5New.first_mapped_physical _
      (History5.historyMap_injective base base_pool_nodup 0 (by decide))).1
  · simp only [Rolling1588.packAtTick,if_neg first]
    split
    · have due := History5.packDue_true i ‹History5.packDue i=true›
      exact mapped_code_physical isA _
        (History5.historyMap_injective base base_pool_nodup (i-5) (by omega))
    · simp [GatePhysical]

theorem forward_physical (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    GatePhysical (forward isA i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have pack : GatePhysical (Rolling1588.Integer.packFirst base isA i) := by
      rw [Rolling1588.Integer.packFirst_base]
      exact pack_physical isA i (by omega)
    rw [forward,gatePhysical_append]
    exact ⟨gatePhysical_rename _ (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr
        ⟨TickRanges.tick_physical base i (by omega) base_pool_nodup,pack⟩),
      ih (i+1) (by omega)⟩

theorem stackForward_physical (isA : Bool) : GatePhysical (stackForward isA) := by
  have old := Rolling1588.stackForward_physical isA
  simp only [Rolling1588.stackForward,gatePhysical_append] at old
  simpa only [stackForward,gatePhysical_append] using
    And.intro (And.intro (forward_physical isA 1 508 (by omega)) old.1.2) old.2

theorem first_physical (isA : Bool) : GatePhysical (firstPhase isA) := by
  have old := Rolling1588.firstPhase_physical isA
  simp only [Rolling1588.firstPhase,gatePhysical_append] at old
  simpa only [firstPhase,tailPhase,gatePhysical_append] using
    And.intro old.1.1 (And.intro (stackForward_physical isA) old.2)

private theorem mapped_run_eq (f : Equiv.Perm Wire) (P Q : Program)
    (s : State) (m : List Bool) (clean : pullState f s=s)
    (same : run P m s=run Q m s) :
    run (renameProgram f P) m s=run (renameProgram f Q) m s := by
  apply pullState_perm_injective f
  rw [run_rename _ f.injective,run_rename _ f.injective,clean]
  exact same

theorem first_hosted_run_eq (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (renameProgram Rolling1588Lifetime.phaseHost (firstPhase isA)) m s=
      run (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase isA)) m s := by
  exact mapped_run_eq Rolling1588Lifetime.phaseHost _ _ s m
    (Rolling1588Lifetime.pull_phase_clean s
      (Rolling1588Lifetime.caller_phase_clean x y s input))
    (first_run_eq isA hn x y hx0 hx s m input)

private theorem append_run_eq_tickgap_phases (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem kernel_run_eq (a b : Bool) (F : Program)
    (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (kernel a b F) m s=run (oldKernel a b F) m s := by
  have records :
      measurementCount (renameProgram Rolling1588Lifetime.phaseHost (firstPhase a))=
        measurementCount (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(first_metrics a).2.1]
  simpa only [kernel,oldKernel] using append_run_eq_tickgap_phases
    (renameProgram Rolling1588Lifetime.phaseHost (firstPhase a))
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a))
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b)) s m records
    (fun r=>first_hosted_run_eq a hn x y hx0 hx s r input)

theorem kernel_metrics (a b : Bool) (F : Program) :
    toffoliCount (kernel a b F)+62=toffoliCount (oldKernel a b F) ∧
      measurementCount (kernel a b F)=measurementCount (oldKernel a b F) ∧
      gateSlots (kernel a b F) ≤ gateSlots (oldKernel a b F) := by
  have first := first_metrics a
  simp only [kernel,oldKernel,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

private theorem mapped_append_support (f : Wire→Wire) (P Q R : Program)
    (first : wires P⊆wires Q) :
    wires (renameProgram f P++R)⊆wires (renameProgram f Q++R) := by
  rw [wires_append,wires_append,renameProgram_support,renameProgram_support]
  exact Finset.union_subset_union
    (Finset.image_mono f first) (Finset.Subset.refl _)

theorem kernel_support (a b : Bool) (F : Program) :
    wires (kernel a b F)⊆wires (oldKernel a b F) := by
  simpa only [kernel,oldKernel] using
    mapped_append_support Rolling1588Lifetime.phaseHost
      (firstPhase a) (Rolling1588.firstPhase a)
      (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b)) (first_support a)

theorem kernel_physical (a b : Bool) (F : Program) (field : GatePhysical F) :
    GatePhysical (kernel a b F) := by
  simpa only [kernel,gatePhysical_append] using
    And.intro (Rolling1588Lifetime.phase_physical _ (first_physical a))
      (And.intro field
        (Rolling1588Lifetime.phase_physical _ (Rolling1588.lastPhase_physical b)))

theorem kernel_entry_correct (F : Program) (raw : EntryCorrect (oldKernel true false F)) :
    EntryCorrect (kernel true false F) := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actual := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  rw [kernel_run_eq true false F hn x _ hx0 hx t m actual]
  exact raw hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half

theorem kernel_exit_correct (F : Program) (raw : ExitCorrect (oldKernel false true F)) :
    ExitCorrect (kernel false true F) := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  rw [kernel_run_eq false true F hn x Y.val hx0 hx s m input]
  exact raw hn hlo ho hf x Y hx0 hx s m input hg hs

theorem entry_correct : EntryCorrect entryKernel := by
  have old : EntryCorrect (oldKernel true false Rolling1588.entryFieldHosted) := by
    simpa only [oldKernel,Rolling1588.entryKernel] using Rolling1588.entry_correct
  simpa only [entryKernel] using kernel_entry_correct Rolling1588.entryFieldHosted old

theorem exit_correct : ExitCorrect exitKernel := by
  have old : ExitCorrect (oldKernel false true Rolling1588.exitFieldHosted) := by
    simpa only [oldKernel,Rolling1588.exitKernel] using Rolling1588.exit_correct
  simpa only [exitKernel] using kernel_exit_correct Rolling1588.exitFieldHosted old

private theorem metrics_of_shapes (P Q A B : Program)
    (left : P=A) (right : Q=B)
    (metrics : toffoliCount A+62=toffoliCount B ∧
      measurementCount A=measurementCount B ∧ gateSlots A ≤ gateSlots B) :
    toffoliCount P+62=toffoliCount Q ∧
      measurementCount P=measurementCount Q ∧ gateSlots P ≤ gateSlots Q := by
  cases left
  cases right
  exact metrics

theorem entryKernel_metrics :
    toffoliCount entryKernel+62=toffoliCount Rolling1588.entryKernel ∧
      measurementCount entryKernel=measurementCount Rolling1588.entryKernel ∧
      gateSlots entryKernel ≤ gateSlots Rolling1588.entryKernel := by
  have left : entryKernel=kernel true false Rolling1588.entryFieldHosted := by
    unfold entryKernel
    rfl
  have right : Rolling1588.entryKernel=oldKernel true false Rolling1588.entryFieldHosted := by
    unfold Rolling1588.entryKernel oldKernel
    rfl
  exact metrics_of_shapes entryKernel Rolling1588.entryKernel
    (kernel true false Rolling1588.entryFieldHosted)
    (oldKernel true false Rolling1588.entryFieldHosted) left right
    (kernel_metrics true false Rolling1588.entryFieldHosted)

theorem exitKernel_metrics :
    toffoliCount exitKernel+62=toffoliCount Rolling1588.exitKernel ∧
      measurementCount exitKernel=measurementCount Rolling1588.exitKernel ∧
      gateSlots exitKernel ≤ gateSlots Rolling1588.exitKernel := by
  have left : exitKernel=kernel false true Rolling1588.exitFieldHosted := by
    unfold exitKernel
    rfl
  have right : Rolling1588.exitKernel=oldKernel false true Rolling1588.exitFieldHosted := by
    unfold Rolling1588.exitKernel oldKernel
    rfl
  exact metrics_of_shapes exitKernel Rolling1588.exitKernel
    (kernel false true Rolling1588.exitFieldHosted)
    (oldKernel false true Rolling1588.exitFieldHosted) left right
    (kernel_metrics false true Rolling1588.exitFieldHosted)

theorem entryKernel_support_subset : wires entryKernel⊆wires Rolling1588.entryKernel := by
  simpa only [entryKernel,oldKernel,Rolling1588.entryKernel] using
    kernel_support true false Rolling1588.entryFieldHosted

theorem exitKernel_support_subset : wires exitKernel⊆wires Rolling1588.exitKernel := by
  simpa only [exitKernel,oldKernel,Rolling1588.exitKernel] using
    kernel_support false true Rolling1588.exitFieldHosted

theorem entryKernel_support : wires entryKernel⊆OB5Support.logicalSites :=
  entryKernel_support_subset.trans Rolling1588.entryKernel_support

theorem exitKernel_support : wires exitKernel⊆OB5Support.logicalSites :=
  exitKernel_support_subset.trans Rolling1588.exitKernel_support

theorem entryKernel_physical : GatePhysical entryKernel := by
  simpa only [entryKernel] using
    kernel_physical true false Rolling1588.entryFieldHosted Rolling1588.entryFieldHosted_physical

theorem exitKernel_physical : GatePhysical exitKernel := by
  simpa only [exitKernel] using
    kernel_physical false true Rolling1588.exitFieldHosted Rolling1588.exitFieldHosted_physical

theorem entryKernel_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_free i hi (entryKernel_support_subset used)

theorem exitKernel_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_free i hi (exitKernel_support_subset used)

theorem entryKernel_768_free : base 768∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_768_free (entryKernel_support_subset used)
theorem exitKernel_768_free : base 768∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_768_free (exitKernel_support_subset used)
theorem entryKernel_718_free : base 718∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_718_free (entryKernel_support_subset used)
theorem exitKernel_718_free : base 718∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_718_free (exitKernel_support_subset used)
theorem entryKernel_719_free : base 719∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_719_free (entryKernel_support_subset used)
theorem exitKernel_719_free : base 719∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_719_free (exitKernel_support_subset used)
theorem entryKernel_760_free : base 760∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_760_free (entryKernel_support_subset used)
theorem exitKernel_760_free : base 760∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_760_free (exitKernel_support_subset used)

end ECDSAAdd.Entrant.Rolling1588TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1TickGap =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Final
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588TickGapPhases

/-! E1 entries and the reflected square are unchanged. Only the two
forward tails use the checked TickGap program. Both inverse phases stay. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1TickGap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def restE (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase true)++
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))

def restX (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false)++
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))

def entryStage (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky++E1QubitPlacement.entryM L kx++restE L

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  ReflectionE1.squareEntry L k++restX L++exitY L cy

theorem entry_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry Rolling1588TickGap.entryKernel L=
      E1QubitPlacement.tickF L++restE L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,Rolling1588TickGap.entryKernel,
    Rolling1588TickGap.kernel,Rolling1588TickGap.firstPhase,restE,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem exit_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L=
      E1QubitPlacement.tickF L++restX L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,Rolling1588TickGap.exitKernel,
    Rolling1588TickGap.kernel,Rolling1588TickGap.firstPhase,restX,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

section CorrectStages
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem entryStage_step (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStage L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  have add:=fastStep_addX L hw hn X Y G origin kx
  have divide:=division_step Rolling1588TickGap.entryKernel Rolling1588TickGap.entryKernel_support
    Rolling1588TickGap.entry_correct L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior:=add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky++E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx++fusedY L ky++E1QubitPlacement.tickF L)
    (R:=restE L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryStage,division,entry_split,List.append_assoc] using prior

theorem secondStage_step (X Y k cy : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStage L k cy)
      (PointDialogValues L Z (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=fusedMultiply_step L hw hn
    (FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L)
    (exit_correct Rolling1588TickGap.exitKernel Rolling1588TickGap.exitKernel_support
      Rolling1588TickGap.exit_correct L hw hn)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=ReflectionE1.squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=restX L++exitY L cy)
  · intro s v m1 m2
    exact ReflectionE1.squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [secondStage,fusedMultiply,exit_split,List.append_assoc,Z] using prior

end CorrectStages

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStage L (-cx) (-cy)++secondStage L (ReflectionE1.correction cx) cy++fastConstNeg L cx

def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L++renameProgram (swapF L) (generic L cx cy)++clrF L

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L++mid L cx cy++zrep L

theorem gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    gen L cx cy=GenericQ5Geometry.wrapG L (generic L cx cy) := rfl

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStage_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  have finish:=fastStep_negX L hw hn d (a*d-cy) true origin cx
  simp only [if_true] at finish
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at finish
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at second finish
  exact (first.seq second).seq finish

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStage_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have finish:=fastStep_negX L hw hn X Y false origin cx
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second finish
  rw [back] at second
  exact (first.seq second).seq finish


theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midFFused_values L hw hn cx cy 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end Correct
attribute [local irreducible] restE restX entryStage secondStage generic mid gen
  ReflectionE1.restE ReflectionE1.restX ReflectionE1.tailP ReflectionE1.generic ReflectionE1.gen
  Rolling1588TickGap.tailPhase Rolling1588TickGap.stackForward Rolling1588.stackForward
  Rolling1588.firstPhase Rolling1588.lastPhase Rolling1588.entryFieldHosted Rolling1588.exitFieldHosted

private theorem relation_of_shapes (R : Program→Program→Prop) (P Q A B : Program)
    (left : P=A) (right : Q=B) (fact : R A B) : R P Q := by
  cases left
  cases right
  exact fact

private theorem fact_of_shape (R : Program→Prop) (P Q : Program)
    (shape : P=Q) (fact : R Q) : R P := by
  cases shape
  exact fact

private def Facts (n : Nat) (P Q : Program) : Prop :=
  toffoliCount P+n=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
    gateSlots P ≤ gateSlots Q ∧ wires P⊆wires Q

private theorem append_facts (P Q C : Program)
    (count : toffoliCount P+62=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
      gateSlots P ≤ gateSlots Q) (sub : wires P⊆wires Q) : Facts 62 (P++C) (Q++C) := by
  simp only [Facts,toffoliCount_append,measurementCount_append,gateSlots_append,wires_append]
  exact ⟨by omega,by omega,by omega,Finset.union_subset_union sub (Finset.Subset.refl _)⟩

private theorem tail_facts (a : Bool) :
    Facts 62 (Rolling1588TickGap.tailPhase a) (ReflectionE1.tailP a) := by
  apply relation_of_shapes (Facts 62) _ _
    (Rolling1588TickGap.stackForward a++skywalkArithmeticClear base)
    (Rolling1588.stackForward a++skywalkArithmeticClear base)
  · unfold Rolling1588TickGap.tailPhase
    rfl
  · unfold ReflectionE1.tailP
    rfl
  · exact append_facts _ _ _ (Rolling1588TickGap.stackForward_metrics a)
      (Rolling1588TickGap.stackForward_support a)

private def restContext (f g : Wire→Wire) (P R : Program) : Program :=
  renameProgram f (renameProgram g P++R)

private theorem rest_facts (f g : Wire→Wire) (P Q R : Program) (h : Facts 62 P Q) :
    Facts 62 (restContext f g P R) (restContext f g Q R) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (restContext f g P R)⊆wires (restContext f g Q R) := by
    simp only [restContext,renameProgram_support,wires_append]
    exact Finset.image_mono f
      (Finset.union_subset_union (Finset.image_mono g hw) (Finset.Subset.refl _))
  simp only [Facts,restContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem restE_facts (L : ControlledPointLayout) :
    Facts 62 (restE L) (ReflectionE1.restE L) := by
  apply relation_of_shapes (Facts 62) _ _
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase true)
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (ReflectionE1.tailP true)
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))
  · unfold restE restContext
    rfl
  · unfold ReflectionE1.restE restContext
    rfl
  · exact rest_facts _ _ _ _ _ (tail_facts true)

private theorem restX_facts (L : ControlledPointLayout) :
    Facts 62 (restX L) (ReflectionE1.restX L) := by
  apply relation_of_shapes (Facts 62) _ _
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false)
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (ReflectionE1.tailP false)
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))
  · unfold restX restContext
    rfl
  · unfold ReflectionE1.restX restContext
    rfl
  · exact rest_facts _ _ _ _ _ (tail_facts false)

private def stagesContext (Y M E S X EY N : Program) : Program :=
  (Y++M++E)++(S++X++EY)++N

private theorem stages_facts (Y M E E0 S X X0 EY N : Program)
    (entry : Facts 62 E E0) (exit : Facts 62 X X0) :
    Facts 124 (stagesContext Y M E S X EY N) (stagesContext Y M E0 S X0 EY N) := by
  rcases entry with ⟨et,em,es,ew⟩
  rcases exit with ⟨xt,xm,xs,xw⟩
  have sub : wires (stagesContext Y M E S X EY N)⊆
      wires (stagesContext Y M E0 S X0 EY N) := by
    simp only [stagesContext,wires_append]
    exact Finset.union_subset_union
      (Finset.union_subset_union
        (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
          (Finset.Subset.refl _)) ew)
        (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) xw)
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,stagesContext,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy=stagesContext (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (exitY L cy) (fastConstNeg L cx) := by
  unfold generic entryStage secondStage stagesContext
  rfl

private theorem old_generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    ReflectionE1.generic L cx cy=stagesContext (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx) := by
  unfold ReflectionE1.generic ReflectionE1.entryStage ReflectionE1.secondStage stagesContext
  rfl

private theorem generic_facts (L : ControlledPointLayout) (cx cy : Fp) :
    Facts 124 (generic L cx cy) (ReflectionE1.generic L cx cy) := by
  exact relation_of_shapes (Facts 124) _ _ _ _
    (generic_shape L cx cy) (old_generic_shape L cx cy)
    (stages_facts (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx)
      (restE_facts L) (restX_facts L))

theorem generic_support_subset (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (ReflectionE1.generic L cx cy) :=
  (generic_facts L cx cy).2.2.2

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (generic_support_subset L cx cy).trans (ReflectionE1.generic_sites L hw hn cx cy)

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) :=
  fun used=>ReflectionE1.generic_free L hw hn cx cy i hi (generic_support_subset L cx cy used)

private theorem suffix_physical (P Q R : Program) (shape : P=Q++R)
    (physical : GatePhysical P) : GatePhysical R := by
  rw [shape,gatePhysical_append] at physical
  exact physical.2

private theorem restE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restE L) := by
  have physical := placed_physical Rolling1588TickGap.entryKernel
    Rolling1588TickGap.entryKernel_support Rolling1588TickGap.entryKernel_physical L hw hn
  have entryPhysical : GatePhysical (FrontierEntry1591Callers.entry Rolling1588TickGap.entryKernel L) :=
    fact_of_shape GatePhysical _ _ (by unfold FrontierEntry1591Callers.entry;rfl) physical
  exact suffix_physical _ _ _ (entry_split L) entryPhysical

private theorem restX_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restX L) := by
  have physical := placed_physical Rolling1588TickGap.exitKernel
    Rolling1588TickGap.exitKernel_support Rolling1588TickGap.exitKernel_physical L hw hn
  have exitPhysical : GatePhysical (FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L) :=
    fact_of_shape GatePhysical _ _ (by unfold FrontierEntry1591Callers.exit;rfl) physical
  exact suffix_physical _ _ _ (exit_split L) exitPhysical

private theorem stages_physical (Y M E E0 S X X0 EY N : Program)
    (old : GatePhysical (stagesContext Y M E0 S X0 EY N))
    (entry : GatePhysical E) (exit : GatePhysical X) :
    GatePhysical (stagesContext Y M E S X EY N) := by
  simp only [stagesContext,gatePhysical_append] at old ⊢
  exact And.intro
    (And.intro (And.intro old.1.1.1 entry)
      (And.intro (And.intro old.1.2.1.1 exit) old.1.2.2)) old.2

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old := fact_of_shape GatePhysical _ _ (old_generic_shape L cx cy).symm
    (ReflectionE1.generic_physical L hw hn cx cy)
  exact fact_of_shape GatePhysical _ _ (generic_shape L cx cy)
    (stages_physical (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx) old
      (restE_physical L hw hn) (restX_physical L hw hn))

private def wrapContext (Z C : Program) (f : Wire→Wire) (P : Program) : Program :=
  Z++(C++renameProgram f P++C)++Z

private theorem wrap_facts (Z C : Program) (f : Wire→Wire) (P Q : Program)
    (h : Facts 124 P Q) : Facts 124 (wrapContext Z C f P) (wrapContext Z C f Q) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (wrapContext Z C f P)⊆wires (wrapContext Z C f Q) := by
    simp only [wrapContext,wires_append,renameProgram_support]
    exact Finset.union_subset_union
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union
          (Finset.union_subset_union (Finset.Subset.refl _) (Finset.image_mono f hw))
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,wrapContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem gen_facts (L : ControlledPointLayout) (cx cy : Fp) :
    Facts 124 (gen L cx cy) (ReflectionE1.gen L cx cy) := by
  apply relation_of_shapes (Facts 124) _ _
    (wrapContext (zrep L) (clrF L) (swapF L) (generic L cx cy))
    (wrapContext (zrep L) (clrF L) (swapF L) (ReflectionE1.generic L cx cy))
  · unfold gen mid wrapContext
    rfl
  · unfold ReflectionE1.gen ReflectionE1.mid wrapContext
    rfl
  · exact wrap_facts _ _ _ _ _ (generic_facts L cx cy)

theorem gen_metrics (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+124=toffoliCount (ReflectionE1.gen L cx cy) ∧
    measurementCount (gen L cx cy)=measurementCount (ReflectionE1.gen L cx cy) ∧
    gateSlots (gen L cx cy) ≤ gateSlots (ReflectionE1.gen L cx cy) :=
  ⟨(gen_facts L cx cy).1,(gen_facts L cx cy).2.1,(gen_facts L cx cy).2.2.1⟩

theorem gen_support_subset (L : ControlledPointLayout) (cx cy : Fp) :
    wires (gen L cx cy)⊆wires (ReflectionE1.gen L cx cy) := (gen_facts L cx cy).2.2.2

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L cx cy).trans (ReflectionE1.gen_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have g:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append] using And.intro (And.intro z (And.intro (And.intro c g) c)) z

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1588 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp)) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

private theorem wrapper_facts (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Facts 124 P Q) :
    toffoliCount (Edges.wrapper L C cy P)+124=toffoliCount (Edges.wrapper L C cy Q) ∧
    measurementCount (Edges.wrapper L C cy P)=measurementCount (Edges.wrapper L C cy Q) ∧
    gateSlots (Edges.wrapper L C cy P) ≤ gateSlots (Edges.wrapper L C cy Q) := by
  rcases h with ⟨ht,hm,hs,_⟩
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 2151582 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout cx cy)).1
  have old:=ReflectionE1.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 1499214 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout cx cy)).2.1
  have old:=ReflectionE1.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 50169199+Rolling1588.slotGrowth := by
  have diff:=(wrapper_facts layout C cy _ _ (gen_facts layout cx cy)).2.2
  have old:=ReflectionE1.wrapper_slots C cx cy
  omega

end ECDSAAdd.Entrant.ReflectionE1TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1TickGapFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1TickGap

/-! E1/reflected Q1588 point with the two checked TickGap forward tails. -/
namespace ECDSAAdd.Entrant.ReflectionE1TickGap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151582,1499214,1588,50169199+Rolling1588.slotGrowth⟩

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
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2151582 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1499214 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50169199+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1499214
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50169199+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C


end ECDSAAdd.Entrant.ReflectionE1TickGap
end -- original module boundary

-- Checked Low48 dependencies follow; the selected reflected prefix retains both checked TickGap tails.

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Square =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareResources
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Square

/-! Only the retained E1 square prefix changes. The reflected entry and all maps stay fixed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1Low48Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

abbrev K : Nat := ControlLoan1589BFFold.K

def core (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.branchCK L ext control++LowZero18Square.branchBF L ext control++
    LowZero18Square.branchAF L ext control

def fastCore (L : ControlledPointLayout) : Program :=
  core L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def program (L : ControlledPointLayout) : Program :=
  SquareCarryLoan719BF.place L (fastCore L)

theorem raw_split (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) :
    LowZero18Square.raw L ext control=core L ext control++LowZero18Square.reflection L ext := rfl

theorem program_split (L : ControlledPointLayout) :
    LowZero18Square.program L=program L++ReflectionE1Square.reflectedTail L := by
  change SquareCarryLoan719BF.place L (LowZero18Square.raw L.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext L) L.core.generic)=
    SquareCarryLoan719BF.place L (core L.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext L) L.core.generic)++
    SquareCarryLoan719BF.place L (SquareCarryLoan719BF.reflection
      L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))
  rw [raw_split,ReflectionE1Square.place_append]
  rfl

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
  have stepC : Triple (SquareFrame L.core.out s.basis O) (LowZero18Square.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := LowZero18Square.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (LowZero18Square.branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := LowZero18Square.branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (LowZero18Square.branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := LowZero18Square.branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
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
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (OwnDiagAll12Square.kext_mem L hw q hq))
  have extOK:=OwnDiagAll12Square.kext_ok L hw hn
  have hext : ECDSAAdd.Entrant.ExtOK K L.core.generic (OwnDiagAll12Square.kext L) :=
    ⟨extOK.nodup,extOK.away,extOK.len⟩
  have kernel := raw_core_correct K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean hext hz
  simpa only [fastCore,hb,hp,pow_two] using kernel


private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

theorem fastCore_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  have fresh:=fastCore_correct L hw hn X.val Y.val G X.isLt s m v.generic v.x v.y v.clean
  refine ⟨fresh.1,?_,fresh.2.2⟩
  have hK : ((SquareCarryLoan719BF.K:Nat):Fp).val=SquareCarryLoan719BF.K :=
    ZMod.val_natCast_of_lt (by norm_num [SquareCarryLoan719BF.K,ControlLoan1589BFFold.K,p])
  rw [ZMod.val_add,sub_val]
  cases G
  · simpa using fresh.2.1
  · simpa [ZMod.val_mul,hK,K,SquareCarryLoan719BF.K] using fresh.2.1

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
  have eq:=ReflectionE1Square.place_run_eq L hw (fastCore L) s m v.clean (by rw [heq];exact clean)
  change run (program L) m s=run (fastCore L) m s at eq
  rw [eq,heq]
  exact result

theorem cleanup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    regValue L.dialogPool (run (program L) m s).basis=0 := by
  have result:=boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (program L) m s=out := ⟨_,rfl⟩
  rw [heq] at result ⊢
  exact (regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq))).trans v.clean

/-- This comparison is separate from the direct boundary proof. -/
theorem run_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (mNew mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) mNew s=run (ReflectionE1Square.program L) mOld s := by
  obtain ⟨a,ha⟩ : ∃a : State,run (program L) mNew s=a := ⟨_,rfl⟩
  obtain ⟨b,hb⟩ : ∃b : State,run (ReflectionE1Square.program L) mOld s=b := ⟨_,rfl⟩
  have fresh:=boundary L hw hn X Y G origin s mNew v
  have prior:=ReflectionE1Square.boundary L hw hn X Y G origin s mOld v
  rw [ha] at fresh
  rw [hb] at prior
  rw [ha,hb]
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · funext q
    by_cases hx : q∈L.point.x
    · exact (regValue_eq_iff _ _ _).mp (fresh.2.1.trans prior.2.1.symm) q hx
    · exact (fresh.2.2 q hx).trans (prior.2.2 q hx).symm

private theorem window_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (LowZero18Square.withLowK2 L ext control src dst body)+66+5*(if src.length=128 then 0 else 1)=
      toffoliCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) ∧
    measurementCount (LowZero18Square.withLowK2 L ext control src dst body)+24+4*(if src.length=128 then 0 else 1)=
      measurementCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have a:=LowZero18Square.withLowK2_counts_diff L hw ext control src dst body h128 h129 hd he
  have b:=LowZero18Square.withLowK2_counts_diff L hw ext control src dst body h128 h129 hd he
  constructor <;> omega

private theorem window_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (LowZero18Square.withLowK2 L ext control src dst body)⊆
      wires (SquareCarryLoan719BF.withLowK2 L ext control src dst body) :=
  LowZero18Square.withLowK2_support_subset L hw ext control src dst body h128 h129 hd he

private theorem window_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (SquareCarryLoan719BF.withLowK2 L ext control src dst body) :=
  LowZero18Square.withLowK2_slots_le L hw ext control src dst body h128 h129 hd he

private theorem core_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    toffoliCount (core L ext control)+243=toffoliCount (ReflectionE1Square.core L ext control) ∧
    measurementCount (core L ext control)+85=measurementCount (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_counts L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_counts L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_counts L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 2 2
    (QRel.bodyCTail_rel L hw control).1 (QRel.bodyCTail_rel L hw control).2.1 (QRel.bodyCTail_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.high (L.core.product.take 256) _ _ 4 4
    (QRel.bBody_rel L hw control).1 (QRel.bBody_rel L hw control).2.1 (QRel.bBody_rel L hw control).2.2
  obtain ⟨a1,a2,a3,a4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.low (L.core.product.take 256) _ _ 3 3
    (QRel.aBody_rel L hw control).1 (QRel.aBody_rel L hw control).2.1 (QRel.aBody_rel L hw control).2.2
  rw [if_neg (show ¬L.core.sum.length=128 by omega)] at c
  rw [if_pos high] at b
  rw [if_pos low] at a
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,toffoliCount_append,measurementCount_append]
  constructor <;> omega

private theorem core_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    wires (core L ext control)⊆wires (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_support L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_support L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_support L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 2 2
    (QRel.bodyCTail_rel L hw control).1 (QRel.bodyCTail_rel L hw control).2.1 (QRel.bodyCTail_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.high (L.core.product.take 256) _ _ 4 4
    (QRel.bBody_rel L hw control).1 (QRel.bBody_rel L hw control).2.1 (QRel.bBody_rel L hw control).2.2
  obtain ⟨a1,a2,a3,a4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.low (L.core.product.take 256) _ _ 3 3
    (QRel.aBody_rel L hw control).1 (QRel.aBody_rel L hw control).2.1 (QRel.aBody_rel L hw control).2.2
  have k3 := q3.trans k3
  have b := b3.trans b
  have a := a3.trans a
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact k3.trans c | exact c | exact b | exact a | exact Finset.Subset.refl _

private theorem core_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (core L ext control)≤Challenge.gateSlots (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_slots L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b:=window_slots L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_slots L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 2 2
    (QRel.bodyCTail_rel L hw control).1 (QRel.bodyCTail_rel L hw control).2.1 (QRel.bodyCTail_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.high (L.core.product.take 256) _ _ 4 4
    (QRel.bBody_rel L hw control).1 (QRel.bBody_rel L hw control).2.1 (QRel.bBody_rel L hw control).2.2
  obtain ⟨a1,a2,a3,a4⟩ := LowZero18Square.withLowK2_body_rel L ext control L.core.low (L.core.product.take 256) _ _ 3 3
    (QRel.aBody_rel L hw control).1 (QRel.aBody_rel L hw control).2.1 (QRel.aBody_rel L hw control).2.2
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,Challenge.gateSlots_append]
  omega

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+243=toffoliCount (ReflectionE1Square.program L) ∧
    measurementCount (program L)+85=measurementCount (ReflectionE1Square.program L) := by
  have h:=core_counts_diff L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,ReflectionE1Square.program,fastCore,ReflectionE1Square.fastCore,
    (ReflectionE1Square.place_counts _ _).1,(ReflectionE1Square.place_counts _ _).2] using h

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=51761 ∧ measurementCount (program L)=52735 := by
  have a:=counts_diff L hw
  have b:=ReflectionE1Square.counts L hw
  constructor <;> omega

theorem support_subset (L : ControlledPointLayout) (hw : L.Widths) :
    wires (program L)⊆wires (ReflectionE1Square.program L) := by
  unfold program ReflectionE1Square.program SquareCarryLoan719BF.place
  repeat' apply OneFlagReplay.rename_subset
  exact core_support_subset L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L hw).trans (ReflectionE1Square.support L hw hn)

theorem free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program L) :=
  fun used=>ReflectionE1Square.free L hw hn i hi (support_subset L hw used)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  have full:=LowZero18Square.physical L hw hn
  rw [program_split,gatePhysical_append] at full
  exact full.1

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (ReflectionE1Square.program L) := by
  have h:=core_slots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,ReflectionE1Square.program,fastCore,ReflectionE1Square.fastCore,
    SquareCarryLoan719BF.place,Baselines.rename_gateSlots] using h

end ECDSAAdd.Entrant.ReflectionE1Low48Square
end -- original module boundary


-- ===== R2 (sqep component): square with retired poolWire 760 =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


/-! # Square -/

namespace ECDSAAdd.Entrant.R2SqEp760
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

/-! ## Square: definitions -/

/-- The retired square site: fold-pad bit 239 (= `ktmp[108]`, carry #239 of every reflected core
adder; physically `poolWire 760`). -/
def sqRet (L : CuccaroStreamedSquareWideLayout) : Wire := L.foldPad.getD 239 0
/-- Its body host: extension wire 130 (physically `poolWire 1363`). -/
def sqHost (ext : List Wire) : Wire := ext.getD 130 0
def sqSwap (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) : Equiv.Perm Wire :=
  Equiv.swap (sqRet L) (sqHost ext)
def bodySwap (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (B : Program) : Program :=
  renameProgram (sqSwap L ext) B

def branchCK760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagAll12Square.gPrep L++
    LowZero18Square.withLowK2 L ext control L.core.sum L.core.product
      (bodySwap L ext (CodexCKAccTail.bodyCTailTq L control))++
    OwnDiagAll12Square.gClear L

def branchBF760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.withLowK2 L ext control L.core.high (L.core.product.take 256)
    (bodySwap L ext (ControlLoan1589BFFold.bBodyTq L control))

def branchAF760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.withLowK2 L ext control L.core.low (L.core.product.take 256)
    (bodySwap L ext (ControlLoan1589BFFold.aBodyTq L control))

def core760 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK760 L ext control++branchBF760 L ext control++branchAF760 L ext control

def fastCore760 (L : ControlledPointLayout) : Program :=
  core760 L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

/-- The new square: `ReflectionE1Low48Square.program` with the three body swaps. -/
def program760 (L : ControlledPointLayout) : Program :=
  SquareCarryLoan719BF.place L (fastCore760 L)

/-! ## Square: positions of the two sites -/

section Sites
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
include hw

theorem foldPad_length : L.foldPad.length=254 := by
  simp [foldPad,hw.core.pad,hw.overflowPad]

omit hw in
theorem sqRet_ktmp : sqRet L=(LowZero18LowK.ktmp L).getD 108 0 := by
  simp only [sqRet,LowZero18LowK.ktmp,List.getD_eq_getElem?_getD,List.getElem?_drop]

theorem sqRet_mem_ktmpTail : sqRet L∈(LowZero18LowK.ktmp L).drop 99 := by
  rw [sqRet_ktmp L]
  have len := LowZero18LowK.ktmp_length L hw
  rw [List.getD_eq_getElem _ _ (by omega)]
  have h : (LowZero18LowK.ktmp L)[108]'(by omega)=((LowZero18LowK.ktmp L).drop 99)[9]'(by simp; omega) := by
    simp
  rw [h]
  exact List.getElem_mem _

theorem sqRet_mem_overflow : sqRet L∈L.overflowPad := by
  have h : sqRet L=L.overflowPad.getD 111 0 := by
    simp only [sqRet,foldPad,List.getD_eq_getElem?_getD,List.getElem?_append_right
      (show L.core.pad.length≤239 by rw [hw.core.pad]; omega),hw.core.pad]
  rw [h,List.getD_eq_getElem _ _ (by rw [hw.overflowPad]; omega)]
  exact List.getElem_mem _

theorem sqRet_mem_wires : sqRet L∈L.wires := by
  simp only [CuccaroStreamedSquareWideLayout.wires,List.mem_append]
  exact Or.inr (sqRet_mem_overflow L hw)

end Sites

theorem sqHost_mem (ext : List Wire) (he : 300≤ext.length) : sqHost ext∈ext := by
  rw [sqHost,List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

/-- `sqRet` is outside the core layout (it is an overflow-pad site). -/
theorem sqRet_not_core (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) : sqRet L∉L.core.wires := by
  have overflow := sqRet_mem_overflow L hw
  have dis := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.2
  exact fun used=>dis (sqRet L) used (sqRet L) overflow rfl

/-! ## Square: support facts -/

section Support
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)

/-- Everything a LowZero leaf kernel names, except the untouched tail of `ktmp`. -/
def kOuter : List Wire :=
  (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++
    (LowZero18LowK.ktmp L).take 99)++ext

include hn hs hd hx hdx in
theorem ktail_away (q : Wire) (hq : q∈(LowZero18LowK.ktmp L).drop 99) :
    q∉kOuter L control ext src dst := by
  apply kdis (LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx) _ q hq
  intro w
  have e := congrArg (List.count w) (List.take_append_drop 99 (LowZero18LowK.ktmp L))
  rw [List.count_append] at e
  simp only [kOuter,LowZero18LowK.kbig2,List.count_append,List.count_cons] at e ⊢
  omega

private theorem mem_tk {l : List Wire} {n : Nat} {q : Wire} (h : q∈l.take n) : q∈l := List.mem_of_mem_take h
private theorem mem_dr {l : List Wire} {n : Nat} {q : Wire} (h : q∈l.drop n) : q∈l := List.mem_of_mem_drop h
private theorem mem_dt {l : List Wire} {a b : Nat} {q : Wire} (h : q∈(l.drop a).take b) : q∈l.take (a+b) := by
  have e : (l.drop a).take b=(l.take (a+b)).drop a := by rw [List.drop_take]; simp
  rw [e] at h
  exact List.mem_of_mem_drop h

private theorem mem_66 {l : List Wire} {q : Wire} (h : q∈l.take 66) : q∈l.take 99 := by
  have e : l.take 66=(l.take 99).take 66 := by rw [List.take_take]; rfl
  rw [e] at h
  exact List.mem_of_mem_take h

/-- Every wire of the leaf kernel's register inventory lies in `kOuter`. -/
theorem kall_outer (q : Wire) (h : q∈(LowZero18LowK.kg L ext src dst).all) :
    q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons]
  unfold LowZero18LowK.kg at h
  split_ifs at h
  all_goals
    simp only [LowZero18LowK.kgH,LowZero18LowK.kgS,KG.all,KG.X,KRegs.all,LowZero18LowK.oregs,
      LowZero18LowK.iregs,LowZero18LowK.jregsH,LowZero18LowK.jregsS,KRegs.lo,KRegs.dlo,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    repeat' (refine Or.elim h (fun h => ?_) (fun h => ?_))
    all_goals first
      | simp [h]
      | simp [mem_tk h]
      | simp [mem_dr h]
      | simp [mem_tk (mem_tk h)]
      | simp [mem_dr (mem_tk h)]
      | simp [mem_tk (mem_dr h)]
      | simp [mem_dr (mem_tk (mem_tk h))]
      | simp [mem_66 (mem_tk h)]
      | simp [mem_66 (mem_tk (mem_tk h))]
      | simp [mem_dt h]

include hw hn hs hd hx hdx in
theorem sqRet_not_outer : sqRet L∉kOuter L control ext src dst :=
  ktail_away L control hn ext src dst hs hd hx hdx _ (sqRet_mem_ktmpTail L hw)

include hw hn hs hd hx hdx in
theorem sqRet_ne_of_outer (q : Wire) (hq : q∈kOuter L control ext src dst) : sqRet L≠q :=
  fun e => sqRet_not_outer L hw control hn ext src dst hs hd hx hdx (e ▸ hq)

theorem ktmp_eq : OwnDiagLowK.ktmp L=LowZero18LowK.ktmp L := rfl

theorem tk99_outer (q : Wire) (h : q∈(LowZero18LowK.ktmp L).take 99) : q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons]; tauto

theorem ext_outer (q : Wire) (h : q∈ext) : q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append]; tauto

theorem cs_outer (q : Wire) (h : q∈control::(src++L.inputBank.take src.length)) :
    q∈kOuter L control ext src dst := by
  simp only [kOuter,List.mem_append,List.mem_cons] at h ⊢; tauto

include hw in
theorem target_outer : SquareCarryLoan719.target L∈kOuter L control ext src dst := by
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.target L∈(LowZero18LowK.ktmp L).take 99 := by
    change (LowZero18LowK.ktmp L).getD 67 0∈_
    rw [List.getD_eq_getElem _ _ (by omega)]
    have : (LowZero18LowK.ktmp L)[67]'(by omega)=((LowZero18LowK.ktmp L).take 99)[67]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _
  exact tk99_outer L control ext src dst _ m

include hw in
theorem earlyHost_outer : SquareCarryLoan719.earlyHost L∈kOuter L control ext src dst := by
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.earlyHost L∈(LowZero18LowK.ktmp L).take 99 := by
    change (LowZero18LowK.ktmp L).getD 1 0∈_
    rw [List.getD_eq_getElem _ _ (by omega)]
    have : (LowZero18LowK.ktmp L)[1]'(by omega)=((LowZero18LowK.ktmp L).take 99)[1]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _
  exact tk99_outer L control ext src dst _ m

include hw hn hs hd hx hdx in
theorem sqRet_masks :
    sqRet L∉wires (copyRegister (some control) src (L.inputBank.take src.length)) ∧
    sqRet L∉wires (eraseMask control src (L.inputBank.take src.length)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  constructor
  · intro used
    have h := List.mem_toFinset.mp (copyRegister_wires_subset (some control) src (L.inputBank.take src.length) used)
    exact ne _ (cs_outer L control ext src dst _ (by simpa only [Option.toList_some,List.singleton_append,
      List.cons_append,List.append_assoc] using h)) rfl
  · intro used
    have h := List.mem_toFinset.mp (eraseMask_wires_subset control src (L.inputBank.take src.length) used)
    exact ne _ (cs_outer L control ext src dst _ h) rfl

include hw hn hs hd hx hdx in
theorem sqRet_kernels (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (he : 300≤ext.length) :
    sqRet L∉wires (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) ∧
    sqRet L∉wires (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have sup := LowZero18LowK.kg_support L hw ext src dst h128 hsmax hlen he
  have offAll : sqRet L∉((LowZero18LowK.kg L ext src dst).all.toFinset) := fun h =>
    ne _ (kall_outer L control ext src dst _ (List.mem_toFinset.mp h)) rfl
  have fix : SquareCarryLoan719.earlyPerm L (sqRet L)=sqRet L := by
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (ne _ (target_outer L hw control ext src dst))
      (ne _ (earlyHost_outer L hw control ext src dst))
  have mk : sqRet L∉wires (LowZero18KG.make (LowZero18LowK.kg L ext src dst)) := fun h => offAll (sup.1 h)
  have cl : sqRet L∉wires (LowZero18KG.clear (LowZero18LowK.kg L ext src dst)) := fun h => offAll (sup.2 h)
  let K := LowZero18LowK.kg L ext src dst
  let T := K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591
  let C := K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591++K.Q2c
  have o1 : LowZero18KG.make K=K.Q1++T := by simp only [LowZero18KG.make,T,List.append_assoc]
  have n1 : LowZero18Square.make L K=renameProgram (SquareCarryLoan719.earlyPerm L) K.Q1++T := by
    simp only [LowZero18Square.make,LowZero18KG.make,SquareCarryLoan719.patchKG,T,List.append_assoc]
  have o2 : LowZero18KG.clear K=C++K.Q1c := by simp only [LowZero18KG.clear,C,List.append_assoc]
  have n2 : LowZero18Square.clear L K=C++renameProgram (SquareCarryLoan719.earlyPerm L) K.Q1c := by
    simp only [LowZero18Square.clear,LowZero18KG.clear,SquareCarryLoan719.patchKG,C,List.append_assoc]
  rw [o1,wires_append,Finset.mem_union,not_or] at mk
  rw [o2,wires_append,Finset.mem_union,not_or] at cl
  constructor
  · change sqRet L∉wires (LowZero18Square.make L K)
    rw [n1,wires_append,Finset.mem_union,not_or]
    exact ⟨OwnPlusHost.rename_avoid _ _ _ fix mk.1,mk.2⟩
  · change sqRet L∉wires (LowZero18Square.clear L K)
    rw [n2,wires_append,Finset.mem_union,not_or]
    exact ⟨cl.1,OwnPlusHost.rename_avoid _ _ _ fix cl.2⟩

end Support

section Core
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)

include hw in
theorem g_core_support :
    wires (OwnDiagAll12Square.gPrep L)⊆L.core.wires.toFinset ∧
    wires (OwnDiagAll12Square.gClear L)⊆L.core.wires.toFinset := by
  let M : CuccaroStreamedSquareWideLayout := ⟨L.core,L.core.pad.take 126⟩
  have mhw : M.Widths := ⟨hw.core,by simp [M,hw.core.pad]⟩
  have sub : (L.core.cin::M.wires).toFinset⊆L.core.wires.toFinset := by
    intro q used
    have h := List.mem_toFinset.mp used
    rcases List.mem_cons.mp h with h|h
    · subst q
      simp [CuccaroStreamedSquareLayout.wires]
    · change q∈L.core.wires++L.core.pad.take 126 at h
      rcases List.mem_append.mp h with h|h
      · exact List.mem_toFinset.mpr h
      · have hp := List.mem_of_mem_take h
        simp [CuccaroStreamedSquareLayout.wires,hp]
  have support := OwnDiagAll12Square.gSum_support M mhw L.core.cin
  exact ⟨support.1.trans sub,support.2.trans sub⟩

end Core

section Free
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length)

include hext in
theorem sqHost_in : sqHost ext∈ext := sqHost_mem ext hext

include hw hdx hext in
theorem sqHost_ne_target : sqHost ext≠SquareCarryLoan719.target L := by
  intro e
  have len := LowZero18LowK.ktmp_length L hw
  have m : SquareCarryLoan719.target L∈LowZero18LowK.ktmp L := by
    change (LowZero18LowK.ktmp L).getD 67 0∈_
    exact DiagSq.getD_in _ 67 (by omega)
  have w : SquareCarryLoan719.target L∈control::L.wires :=
    List.mem_cons_of_mem _ (LowZero18LowK.ktmp_wires L _ m)
  exact hdx _ (sqHost_in ext hext) (e ▸ w)

include hx hext in
theorem sqHost_ne_ext0 : sqHost ext≠ext.getD 0 0 := by
  intro e
  rw [sqHost,List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  omega

include hw hx hdx hext in
theorem sqHost_fold_free (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqHost ext∉wires (renameProgram (SquareCarryLoan719.foldPerm L ext) B) := by
  rw [SquareCarryLoan719.foldPerm_eq L hw]
  apply OwnPlusHost.rename_avoid _ _ _
    (Equiv.swap_apply_of_ne_of_ne (sqHost_ne_target L hw control ext hdx hext) (sqHost_ne_ext0 ext hx hext))
  exact fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used))

include hw hn hx hdx hext in
theorem sqRet_body_free (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqRet L∉wires (renameProgram (SquareCarryLoan719.foldPerm L ext) (bodySwap L ext B)) := by
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  rw [SquareCarryLoan719.foldPerm_eq L hw]
  apply OwnPlusHost.rename_avoid _ _ _
    (Equiv.swap_apply_of_ne_of_ne (ne _ (target_outer L hw control ext src dst))
      (ne _ (ext_outer L control ext src dst _ (DiagSq.getD_in ext 0 (by omega)))))
  exact swap_free _ _ _ (fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used)))

include hw hn hx hdx hext in
theorem withLowK2_760_free (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    sqRet L∉wires (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B)) := by
  have m := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have k := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen hext
  have f := sqRet_body_free L hw control hn ext hx hdx hext src dst hs hd B hb
  simp only [LowZero18Square.withLowK2,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨m.1,k.1⟩,m.2⟩,f⟩,m.1⟩,k.2⟩,m.2⟩

include hw hn hx hdx hext in
theorem core760_free : sqRet L∉wires (core760 L ext control) := by
  have nd := (List.nodup_cons.mp hn).2
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have hl (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have hh (q : Wire) : L.core.high.count q≤L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := hh q
    simp only [List.count_append]
    omega
  have hs (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := hh q
    simp only [CuccaroStreamedSquareLayout.sum,List.count_append] at h ⊢
    omega
  have hp (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have sa := withLowK2_760_free L hw control hn ext hx hdx hext L.core.low (L.core.product.take 256)
    hl hp (by omega) (by omega) (by simp [hw.core.product,low]) _ (ControlLoan1589BFFold.aBody_supportTq L hw nd control)
  have sb := withLowK2_760_free L hw control hn ext hx hdx hext L.core.high (L.core.product.take 256)
    hb hp (by omega) (by omega) (by simp [hw.core.product,high]) _ (ControlLoan1589BFFold.bBody_supportTq L hw nd control)
  have sc := withLowK2_760_free L hw control hn ext hx hdx hext L.core.sum L.core.product
    hs (fun _=>le_rfl) (by omega) (by omega) (by rw [hw.core.product,sum]) _
    (CodexCKAccTail.bodyCTail_supportTq L hw nd control)
  have coreOff := sqRet_not_core L hw control hn
  have gs := g_core_support L hw
  have gp : sqRet L∉wires (OwnDiagAll12Square.gPrep L) := fun u => coreOff (List.mem_toFinset.mp (gs.1 u))
  have gc : sqRet L∉wires (OwnDiagAll12Square.gClear L) := fun u => coreOff (List.mem_toFinset.mp (gs.2 u))
  simp only [core760,branchCK760,branchBF760,branchAF760,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨gp,sc⟩,gc⟩,sb⟩,sa⟩

end Free

section Placed
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
private theorem pool_getD' (i : Nat) (hi : i<2613) : L.dialogPool.getD i 0=L.core.poolWire i := by
  have shape := pool_block L hw 2613 (le_refl _)
  rw [List.take_of_length_le (by rw [L.dialogPool_length hw])] at shape
  rw [shape,List.getD_eq_getElem _ _ (by simp [wireBlock];omega)]
  simp [wireBlock]

include hw in
theorem sqRet_pool760 : sqRet L.dialogStreamedSquareWide=L.core.poolWire 760 := by
  rw [sqRet_ktmp,← ktmp_eq,SquareCarryLoan719Inventory.ktmp_layout L hw,List.getD_eq_getElem _ _ (by
    simp only [List.length_take,List.length_drop,L.dialogPool_length hw]
    omega)]
  simp only [List.getElem_take,List.getElem_drop,Nat.reduceAdd]
  have bound : 760<L.dialogPool.length := by rw [L.dialogPool_length hw];omega
  have same := pool_getD' L hw 760 (by omega)
  rw [List.getD_eq_getElem L.dialogPool 0 bound] at same
  exact same

theorem sqHost_pool1363 : sqHost (OwnDiagAll12Square.kext L)=L.core.poolWire 1363 := by
  simp [sqHost,OwnDiagAll12Square.kext,wireBlock]

include hw hn in
private theorem pool_fix (k a b : Nat) (hk : k<2613) (ha : a<2613) (hb : b<2613) (na : k≠a) (nb : k≠b) :
    Equiv.swap (L.core.poolWire a) (L.core.poolWire b) (L.core.poolWire k)=L.core.poolWire k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq
    exact na (pool_inj L hw hn k a hk ha eq)
  · intro eq
    exact nb (pool_inj L hw hn k b hk hb eq)

include hw hn in
/-- Every placement map of the square fixes pool sites 760 and 1363. -/
theorem place_fix (k : Nat) (hk : k=760 ∨ k=1363) (P : Program) (free : L.core.poolWire k∉wires P) :
    L.core.poolWire k∉wires (SquareCarryLoan719BF.place L P) := by
  have kb : k<2613 := by omega
  have blockFix : Square5Placement.blockPerm L 202 (L.core.poolWire k)=L.core.poolWire k := by
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) k kb]
    rcases hk with rfl|rfl <;> rfl
  have p0 := OwnPlusHost.rename_avoid _ _ _ blockFix free
  have p1 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 766 1530 kb (by omega) (by omega) (by omega) (by omega)) p0
  have p2 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 765 1531 kb (by omega) (by omega) (by omega) (by omega)) p1
  have p3 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 767 1532 kb (by omega) (by omega) (by omega) (by omega)) p2
  have p4 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 770 1536 kb (by omega) (by omega) (by omega) (by omega)) p3
  have p5 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 1285 1537 kb (by omega) (by omega) (by omega) (by omega)) p4
  have p6 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 1286 1538 kb (by omega) (by omega) (by omega) (by omega)) p5
  have p7 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 769 1539 kb (by omega) (by omega) (by omega) (by omega)) p6
  have p8 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 768 775 kb (by omega) (by omega) (by omega) (by omega)) p7
  have p9 := OwnPlusHost.rename_avoid _ _ _ (pool_fix L hw hn k 718 907 kb (by omega) (by omega) (by omega) (by omega)) p8
  simpa only [SquareCarryLoan719BF.place,OwnPlusSquare.swap,OwnGuardSquare.swap,
    OwnQ4Square.swap,OwnQ5Square.swap,OwnDiagAll12PlacedQ6.swap,OwnDiagAll12PlacedQ7.swap,
    PrefixFrontierSquare1591.swap,Prefix1590Square.swap,ControlLoan1589Square.swap] using p9

include hw hn in
/-- **R2 square deliverable**: the new square never touches physical pool site 760. -/
theorem square760_free : L.core.poolWire 760∉wires (program760 L) := by
  have controlND : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have he := OwnDiagAll12Square.kext_ok L hw hn
  have core := core760_free L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    L.core.generic controlND (OwnDiagAll12Square.kext L) he.nodup he.away he.len
  rw [sqRet_pool760 L hw] at core
  exact place_fix L hw hn 760 (Or.inl rfl) _ core

end Placed

/-! ## Square: counts, slots, physicality, support -/

theorem gatePhysical_rename_iff (e : Equiv.Perm Wire) (P : Program) :
    GatePhysical (renameProgram e P)↔GatePhysical P := by
  constructor
  · intro h i hi
    have hh := h (renameInstr e i) (List.mem_map_of_mem hi)
    cases i <;> simp_all [renameInstr,RecordedQuantum.PhysicalInstr,ECDSAAdd.ProperGate,e.injective.eq_iff]
  · exact gatePhysical_rename e e.injective P

theorem place_physical_iff (L : ControlledPointLayout) (P : Program) :
    GatePhysical (SquareCarryLoan719BF.place L P)↔GatePhysical P := by
  simp only [SquareCarryLoan719BF.place,gatePhysical_rename_iff]

theorem fastCore760_shape (L : ControlledPointLayout) :
    ReflectionE1Low48Square.program L=SquareCarryLoan719BF.place L (ReflectionE1Low48Square.fastCore L) := rfl

theorem program760_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program760 L) := by
  have old := ReflectionE1Low48Square.physical L hw hn
  rw [fastCore760_shape,place_physical_iff] at old
  rw [program760,place_physical_iff]
  simp only [ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,LowZero18Square.withLowK2,
    gatePhysical_append,gatePhysical_rename_iff] at old
  simp only [fastCore760,core760,branchCK760,branchBF760,branchAF760,LowZero18Square.withLowK2,bodySwap,
    gatePhysical_append,gatePhysical_rename_iff]
  exact old

theorem program760_counts (L : ControlledPointLayout) :
    toffoliCount (program760 L)=toffoliCount (ReflectionE1Low48Square.program L) ∧
    measurementCount (program760 L)=measurementCount (ReflectionE1Low48Square.program L) := by
  rw [fastCore760_shape]
  simp only [program760,SquareCarryLoan719BF.place,fastCore760,core760,branchCK760,branchBF760,branchAF760,
    ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,LowZero18Square.withLowK2,bodySwap,
    toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    and_self]

theorem program760_slots (L : ControlledPointLayout) :
    Challenge.gateSlots (program760 L)=Challenge.gateSlots (ReflectionE1Low48Square.program L) := by
  rw [fastCore760_shape]
  simp only [program760,SquareCarryLoan719BF.place,fastCore760,core760,branchCK760,branchBF760,branchAF760,
    ReflectionE1Low48Square.fastCore,ReflectionE1Low48Square.core,LowZero18Square.branchCK,
    LowZero18Square.branchBF,LowZero18Square.branchAF,LowZero18Square.withLowK2,bodySwap,
    Challenge.gateSlots_append,Baselines.rename_gateSlots]

theorem counts_diff760 (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program760 L)+243=toffoliCount (ReflectionE1Square.program L) ∧
    measurementCount (program760 L)+85=measurementCount (ReflectionE1Square.program L) := by
  rw [(program760_counts L).1,(program760_counts L).2]
  exact ReflectionE1Low48Square.counts_diff L hw

theorem slots_le760 (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program760 L)≤Challenge.gateSlots (ReflectionE1Square.program L) := by
  rw [program760_slots]; exact ReflectionE1Low48Square.slots_le L hw

theorem rename_ins (e : Equiv.Perm Wire) (h : Wire) (P Q : Program)
    (sub : wires P⊆insert h (wires Q)) (fix : e h=h) :
    wires (renameProgram e P)⊆insert h (wires (renameProgram e Q)) := by
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (sub hx) with e'|hx'
  · subst x; rw [fix]; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx')

theorem swap_ins (a b : Wire) (P : Program) (hb : b∉wires P) :
    wires (renameProgram (Equiv.swap a b) P)⊆insert b (wires P) :=
  (swap_support a b P hb).trans (Finset.insert_subset_insert _ (Finset.erase_subset _ _))

section SupportNew
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires)
  (hext : 300≤ext.length)

include hw hx hdx hext in
theorem withLowK2_ins (src dst : List Wire) (B : Program) (hb : wires B⊆(control::L.wires).toFinset) :
    wires (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B))⊆
      insert (sqHost ext) (wires (LowZero18Square.withLowK2 L ext control src dst B)) := by
  have bfree : sqHost ext∉wires B := fun used => hdx _ (sqHost_in ext hext) (List.mem_toFinset.mp (hb used))
  have fix : SquareCarryLoan719.foldPerm L ext (sqHost ext)=sqHost ext := by
    rw [SquareCarryLoan719.foldPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (sqHost_ne_target L hw control ext hdx hext) (sqHost_ne_ext0 ext hx hext)
  have body := rename_ins _ _ _ _ (swap_ins (sqRet L) (sqHost ext) B bfree) fix
  intro q hq
  simp only [LowZero18Square.withLowK2,bodySwap,sqSwap,wires_append,Finset.mem_union,Finset.mem_insert] at hq ⊢
  rcases hq with ((((((h|h)|h)|h)|h)|h)|h)
  all_goals first
    | (rcases Finset.mem_insert.mp (body h) with e|e
       · exact Or.inl e
       · tauto)
    | tauto

include hw hn hx hdx hext in
theorem core760_ins : wires (core760 L ext control)⊆
    insert (sqHost ext) (wires (ReflectionE1Low48Square.core L ext control)) := by
  have nd := (List.nodup_cons.mp hn).2
  have a := withLowK2_ins L hw control ext hx hdx hext L.core.low (L.core.product.take 256) _
    (ControlLoan1589BFFold.aBody_supportTq L hw nd control)
  have b := withLowK2_ins L hw control ext hx hdx hext L.core.high (L.core.product.take 256) _
    (ControlLoan1589BFFold.bBody_supportTq L hw nd control)
  have c := withLowK2_ins L hw control ext hx hdx hext L.core.sum L.core.product _
    (CodexCKAccTail.bodyCTail_supportTq L hw nd control)
  intro q hq
  simp only [core760,branchCK760,branchBF760,branchAF760,wires_append,Finset.mem_union] at hq
  simp only [ReflectionE1Low48Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,wires_append,Finset.mem_union,Finset.mem_insert]
  rcases hq with (((h|h)|h)|h)|h
  · tauto
  · rcases Finset.mem_insert.mp (c h) with e|e <;> tauto
  · tauto
  · rcases Finset.mem_insert.mp (b h) with e|e <;> tauto
  · rcases Finset.mem_insert.mp (a h) with e|e <;> tauto

end SupportNew

section SupportPlaced
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw hn in
theorem place_ins (P Q : Program) (sub : wires P⊆insert (L.core.poolWire 1363) (wires Q)) :
    wires (SquareCarryLoan719BF.place L P)⊆insert (L.core.poolWire 1363) (wires (SquareCarryLoan719BF.place L Q)) := by
  have kb : 1363<2613 := by omega
  have blockFix : Square5Placement.blockPerm L 202 (L.core.poolWire 1363)=L.core.poolWire 1363 := by
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) 1363 kb]; rfl
  have f (a b : Nat) (ha : a<2613) (hb : b<2613) (na : 1363≠a) (nb : 1363≠b) :=
    pool_fix L hw hn 1363 a b kb ha hb na nb
  simp only [SquareCarryLoan719BF.place]
  apply rename_ins _ _ _ _ _ (f 718 907 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 768 775 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 769 1539 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 1286 1538 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 1285 1537 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 770 1536 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 767 1532 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 765 1531 (by omega) (by omega) (by omega) (by omega))
  apply rename_ins _ _ _ _ _ (f 766 1530 (by omega) (by omega) (by omega) (by omega))
  exact rename_ins _ _ _ _ sub blockFix

include hw hn in
/-- New square support: the old square's support with site 760 replaced by site 1363. -/
theorem program760_support_subset :
    wires (program760 L)⊆insert (L.core.poolWire 1363)
      ((wires (ReflectionE1Low48Square.program L)).erase (L.core.poolWire 760)) := by
  have controlND : (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have he := OwnDiagAll12Square.kext_ok L hw hn
  have core := core760_ins L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    L.core.generic controlND (OwnDiagAll12Square.kext L) he.nodup he.away he.len
  rw [sqHost_pool1363 L] at core
  have placed := place_ins L hw hn _ _ core
  have free := square760_free L hw hn
  intro q hq
  rcases Finset.mem_insert.mp (placed hq) with e|e
  · exact e ▸ Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_erase.mpr ⟨fun h => free (h ▸ hq),e⟩

include hw hn in
theorem program760_support : wires (program760 L)⊆(OB5Support.sites L).toFinset := by
  have old := ReflectionE1Low48Square.support L hw hn
  intro q hq
  rcases Finset.mem_insert.mp (program760_support_subset L hw hn hq) with e|e
  · subst e
    simp [OB5Support.sites,OB5Support.poolSites,wireBlock]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1363,⟨by omega,by omega⟩,rfl⟩)))))
  · exact old (Finset.mem_of_mem_erase e)

include hw hn in
theorem program760_free_old (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program760 L) := by
  intro used
  rcases Finset.mem_insert.mp (program760_support_subset L hw hn used) with e|e
  · have ib : i<2613 := by simp at hi; omega
    have := pool_inj L hw hn i 1363 ib (by omega) e
    subst this; simp at hi
  · exact ReflectionE1Low48Square.free L hw hn i hi (Finset.mem_of_mem_erase e)

end SupportPlaced

/-! ## Square: the host is clean when the body starts -/

theorem top_bits_zero (r : List Wire) (st : BasisState) (k : Nat) (h : regValue r st<2^k)
    (q : Wire) (hq : q∈r.drop k) : st q=false := by
  by_cases hk : k≤r.length
  · have e := regValue_append (r.take k) (r.drop k) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left hk] at e
    have z : regValue (r.drop k) st=0 := by
      by_contra nz
      have : 2^k≤2^k*regValue (r.drop k) st := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero nz)
      omega
    exact (regValue_zero _ _).mp z q hq
  · rw [List.drop_eq_nil_of_le (by omega)] at hq
    simp at hq

theorem host_not_drop (ext : List Wire) (hx : ext.Nodup) (hext : 300≤ext.length) (k : Nat) (hk : 131≤k) :
    sqHost ext∉ext.drop k := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_drop,sqHost,List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  omega

theorem host_not_take (ext : List Wire) (hx : ext.Nodup) (hext : 300≤ext.length) :
    sqHost ext∉ext.take 130 := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_take,sqHost,List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  simp at hi
  omega

private theorem mem_drop_mono {l : List Wire} {a b : Nat} {q : Wire} (h : q∈l.drop b) (hab : a≤b) :
    q∈l.drop a := by
  have e : l.drop b=(l.drop a).drop (b-a) := by rw [List.drop_drop]; congr 1; omega
  rw [e] at h
  exact List.mem_of_mem_drop h

/-- After copy/make/erase the body host is zero: for 128-bit sources it is outside every kernel
register; for the 129-bit sum it is bit 130 of `T = 2·lo·hi < 2^130`. -/
theorem prefix_host_zero (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (s : State) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (r1 r2 r3 : List Bool) :
    (run (eraseMask control src (L.inputBank.take src.length)) r3
      (run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2
        (run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s))).basis (sqHost ext)=false := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have hostE := sqHost_in ext he
  -- erase does not touch the host
  have eraseOff : sqHost ext∉wires (eraseMask control src (L.inputBank.take src.length)) := by
    intro used
    have h := List.mem_toFinset.mp (eraseMask_wires_subset control src (L.inputBank.take src.length) used)
    rcases List.mem_cons.mp h with h|h
    · exact hdx _ hostE (by simp [h])
    · rcases List.mem_append.mp h with h|h
      · exact extSrc _ hostE h
      · exact extB _ hostE h
  rw [run_preserves_outside _ _ _ _ eraseOff]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
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
  have mkEq := LowZero18Square.make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
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
  rw [mkEq]
  rw [hKR] at mk
  by_cases h : src.length=128
  · -- the host lies in no kernel register
    have notT : sqHost ext∉(LowZero18LowK.oregs L ext src dst).T := by
      intro m
      have m' : sqHost ext∈(ext.take 132).take 130 := by
        simpa [LowZero18LowK.oregs,h] using m
      rw [List.take_take] at m'
      exact host_not_take ext hx he (by simpa using m')
    have notX : sqHost ext∉(LowZero18LowK.kg L ext src dst).X := by
      intro m
      rw [LowZero18LowK.kg,if_pos h] at m
      simp only [LowZero18LowK.kgH,KG.X,LowZero18LowK.iregs,LowZero18LowK.jregsH,List.mem_append,
        List.not_mem_nil,or_false] at m
      rcases m with ((m|m)|(m|m))
      · exact tmpE _ (List.mem_of_mem_drop (List.mem_of_mem_take m)) hostE
      · exact host_not_drop ext hx he 132 (by omega) (List.mem_of_mem_take m)
      · exact host_not_drop ext hx he 198 (by omega) (List.mem_of_mem_take (List.mem_of_mem_take m))
      · exact host_not_drop ext hx he 232 (by omega) (List.mem_of_mem_take m)
    have notD : sqHost ext∉(LowZero18LowK.oregs L ext src dst).dst := fun m =>
      (dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega) : ∀q∈ext,q∉dst) _ hostE m
    rw [mk.2.2.2.2.2.2.2 _ notD notT notX,u0s _ (extB _ hostE)]
    exact ext0 _ hostE
  · -- the host is bit 130 of T = 2·lo·hi < 2^130
    have h129 : src.length=129 := by omega
    have tv := mk.2.2.2.1
    have lo_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).lo u0.basis
    have hi_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).hi u0.basis
    have lol : (LowZero18LowK.oregs L ext src dst).lo.length=64 := by
      simp [LowZero18LowK.oregs,KRegs.lo,sizes.1,h129]
    have hil : (LowZero18LowK.oregs L ext src dst).hi.length=65 := by
      simp [LowZero18LowK.oregs,KRegs.hi,sizes.1,h129]
    rw [lol] at lo_lt
    rw [hil] at hi_lt
    have prod : 2*regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis*
        regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis<2^130 := by
      have := Nat.mul_lt_mul'' lo_lt hi_lt
      have e : (2:Nat)^130=2*(2^64*2^65) := by norm_num
      rw [e,Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left this (by norm_num)
    rw [← tv] at prod
    apply top_bits_zero _ _ 130 prod
    have tl : (LowZero18LowK.oregs L ext src dst).T=ext.take 132 := by
      simp [LowZero18LowK.oregs,h129]
    rw [tl,sqHost,List.getD_eq_getElem _ _ (by omega)]
    have : ext[130]'(by omega)=((ext.take 132).drop 130)[0]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _

/-! ## Square: run equality -/

theorem mid_swap (Pre X Post : Program) (a b : Wire) (s : State) (m : List Bool)
    (ua : (run Pre (m.take (measurementCount Pre)) s).basis a=false)
    (ub : (run Pre (m.take (measurementCount Pre)) s).basis b=false)
    (bX : b∉wires X) (aPost : a∉wires Post)
    (fin : (run (Pre++X++Post) m s).basis a=false) :
    run (Pre++renameProgram (Equiv.swap a b) X++Post) m s=run (Pre++X++Post) m s := by
  have mc := (renameProgram_counts (Equiv.swap a b) X).2
  simp only [run_append,measurementCount_append,mc] at fin ⊢
  have e : List.take (measurementCount Pre) (List.take (measurementCount Pre+measurementCount X) m)=
      List.take (measurementCount Pre) m := by rw [List.take_take]; congr 1; omega
  simp only [e] at fin ⊢
  generalize run Pre (List.take (measurementCount Pre) m) s=u at ua ub fin ⊢
  rw [run_preserves_outside Post _ _ a aPost] at fin
  congr 1
  exact swap_run_eq a b X u _ ua ub fin ((run_preserves_outside X _ u b bX).trans ub)

theorem swaps_commute (a b c d : Wire) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (P : Program) :
    renameProgram (Equiv.swap c d) (renameProgram (Equiv.swap a b) P)=
      renameProgram (Equiv.swap a b) (renameProgram (Equiv.swap c d) P) := by
  rw [renameProgram_comp,renameProgram_comp]
  congr 1
  funext x
  simp only [Function.comp,Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem withLowK2_swap_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (B : Program) (hb : wires B⊆(control::L.wires).toFinset)
    (s : State) (m : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0)
    (fin : (run (LowZero18Square.withLowK2 L ext control src dst B) m s).basis (sqRet L)=false) :
    run (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B)) m s=
      run (LowZero18Square.withLowK2 L ext control src dst B) m s := by
  have masks := sqRet_masks L hw control hn ext src dst hs hd hx hdx
  have kern := sqRet_kernels L hw control hn ext src dst hs hd hx hdx h128 hsmax hlen he
  have ne := sqRet_ne_of_outer L hw control hn ext src dst hs hd hx hdx
  have rt := ne _ (target_outer L hw control ext src dst)
  have r0 := ne _ (ext_outer L control ext src dst _ (DiagSq.getD_in ext 0 (by omega)))
  have ht := sqHost_ne_target L hw control ext hdx he
  have h0 := sqHost_ne_ext0 ext hx he
  have com : renameProgram (SquareCarryLoan719.foldPerm L ext) (bodySwap L ext B)=
      renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B) := by
    rw [SquareCarryLoan719.foldPerm_eq L hw,bodySwap,sqSwap]
    exact swaps_commute _ _ _ _ rt r0 ht h0 B
  let Pre := copyRegister (some control) src (L.inputBank.take src.length)++
    LowZero18Square.make L (LowZero18LowK.kg L ext src dst)++eraseMask control src (L.inputBank.take src.length)
  let Post := copyRegister (some control) src (L.inputBank.take src.length)++
    LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)++eraseMask control src (L.inputBank.take src.length)
  have s0 : LowZero18Square.withLowK2 L ext control src dst B=
      Pre++renameProgram (SquareCarryLoan719.foldPerm L ext) B++Post := by
    simp only [LowZero18Square.withLowK2,Pre,Post,List.append_assoc]
  have s1 : LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B)=
      Pre++renameProgram (Equiv.swap (sqRet L) (sqHost ext)) (renameProgram (SquareCarryLoan719.foldPerm L ext) B)++Post := by
    rw [← com]
    simp only [LowZero18Square.withLowK2,Pre,Post,List.append_assoc]
  rw [s0] at fin
  rw [s1,s0]
  have retPre : sqRet L∉wires Pre := by
    simp only [Pre,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨masks.1,kern.1⟩,masks.2⟩
  have retPost : sqRet L∉wires Post := by
    simp only [Post,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨masks.1,kern.2⟩,masks.2⟩
  have retS : s.basis (sqRet L)=false := by
    apply (regValue_zero _ _).mp hc.pad
    exact DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega)
  apply mid_swap _ _ _ _ _ s m ((run_preserves_outside _ _ _ _ retPre).trans retS) _
    (sqHost_fold_free L hw control ext hx hdx he B hb) retPost fin
  simp only [Pre,run_append]
  exact prefix_host_zero L hw control hn src dst hs hd h128 hsmax hlen ext hx hdx he s hc hzero hz _ _ _

theorem run3 (A W C : Program) (s : State) (m : List Bool) :
    run (A++W++C) m s=run C (m.drop (measurementCount A+measurementCount W))
      (run W ((m.drop (measurementCount A)).take (measurementCount W)) (run A (m.take (measurementCount A)) s)) := by
  simp only [run_append,measurementCount_append]
  have e1 : List.take (measurementCount A) (List.take (measurementCount A+measurementCount W) m)=
      List.take (measurementCount A) m := by rw [List.take_take]; congr 1; omega
  have e2 : List.drop (measurementCount A) (List.take (measurementCount A+measurementCount W) m)=
      List.take (measurementCount W) (List.drop (measurementCount A) m) := by
    rw [List.drop_take]; congr 1; omega
  rw [e1,e2]

theorem withLowK2_swap_mc (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (B : Program) :
    measurementCount (LowZero18Square.withLowK2 L ext control src dst (bodySwap L ext B))=
      measurementCount (LowZero18Square.withLowK2 L ext control src dst B) := by
  simp only [LowZero18Square.withLowK2,bodySwap,measurementCount_append,(renameProgram_counts _ _).2]

section Branches
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire) (control : Wire)
  (hn : (control::L.wires).Nodup)

include hw in
theorem sqRet_not_out (hn' : L.wires.Nodup) : sqRet L∉L.core.out :=
  (L.pairAuxAway hn' (sqRet L) (by
    simp only [List.mem_append]
    exact Or.inl (Or.inl (DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega))))).2

include hw in
theorem sqRet_clean (st : BasisState) (hc : L.PairClean st) : st (sqRet L)=false :=
  (regValue_zero _ _).mp hc.pad _ (DiagSq.getD_in _ 239 (by rw [foldPad_length L hw]; omega))

include hw hn in
theorem branchBF760_run_eq (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchBF760 L ext control) records s=run (LowZero18Square.branchBF L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have old := (LowZero18Square.branchBF_correct L hw ext control hn B O hO s records hb ho hp0 hc he hz).2.2
    (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at old
  exact withLowK2_swap_run_eq L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len _
    (ControlLoan1589BFFold.bBody_supportTq L hw nd control) s records hc dstZero hz old

include hw hn in
theorem branchAF760_run_eq (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchAF760 L ext control) records s=run (LowZero18Square.branchAF L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have old := (LowZero18Square.branchAF_correct L hw ext control hn A O hO s records ha ho hp0 hc he hz).2.2
    (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at old
  exact withLowK2_swap_run_eq L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) ext he.nodup he.away he.len _
    (ControlLoan1589BFFold.aBody_supportTq L hw nd control) s records hc dstZero hz old

end Branches

theorem branchCK760_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hsum : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (branchCK760 L ext control) records s=run (LowZero18Square.branchCK L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  let W := LowZero18Square.withLowK2 L ext control L.core.sum L.core.product (CodexCKAccTail.bodyCTailTq L control)
  let W' := LowZero18Square.withLowK2 L ext control L.core.sum L.core.product
    (bodySwap L ext (CodexCKAccTail.bodyCTailTq L control))
  let mp := measurementCount (OwnDiagAll12Square.gPrep L)
  let u := run (OwnDiagAll12Square.gPrep L) (records.take mp) s
  have prep := OwnDiagAll12Square.gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hsum,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
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
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have gOff : sqRet L∉wires (OwnDiagAll12Square.gClear L) := fun used =>
    sqRet_not_core L hw control hn (List.mem_toFinset.mp ((g_core_support L hw).2 used))
  have old := (LowZero18Square.branchCK_correct L hw ext control hn A B O hO s records ha hsum bound ho hp0 hc he hz).2.2
    (sqRet L) (sqRet_not_out L hw nd)
  rw [sqRet_clean L hw _ hc] at old
  have shapeOld : LowZero18Square.branchCK L ext control=OwnDiagAll12Square.gPrep L++W++OwnDiagAll12Square.gClear L := rfl
  have shapeNew : branchCK760 L ext control=OwnDiagAll12Square.gPrep L++W'++OwnDiagAll12Square.gClear L := rfl
  rw [shapeOld,run3,run_preserves_outside _ _ _ _ gOff] at old
  have mid := withLowK2_swap_run_eq L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len _
    (CodexCKAccTail.bodyCTail_supportTq L hw nd control) u _ cleanU productU hzU old
  rw [shapeNew,shapeOld,run3,run3,withLowK2_swap_mc]
  exact congrArg _ mid

theorem core760_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    run (core760 L ext control) records s=run (ReflectionE1Low48Square.core L ext control) records s := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have keepAll (t : State) (hf : ∀q,q∉L.core.out → t.basis q=s.basis q) :
      regValue L.core.low t.basis=A ∧ regValue L.core.high t.basis=B ∧
      regValue L.core.product t.basis=0 ∧ regValue ext t.basis=0 ∧ L.PairClean t.basis := by
    refine ⟨regValue_congr _ _ _ (fun q hq => hf q (lowAway q hq)),
      regValue_congr _ _ _ (fun q hq => hf q (highAway q hq)),
      (regValue_congr _ _ _ (fun q hq => hf q (List.disjoint_left.mp disProduct hq))).trans hp0,
      (regValue_congr _ _ _ (fun q hq => hf q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz,
      L.squareFrame_clean nd s.basis t.basis _ ⟨rfl,hf⟩ hc⟩
  let CK := LowZero18Square.branchCK L ext control
  let BF := LowZero18Square.branchBF L ext control
  let AF := LowZero18Square.branchAF L ext control
  have mcC : measurementCount (branchCK760 L ext control)=measurementCount CK := by
    simp only [branchCK760,CK,LowZero18Square.branchCK,measurementCount_append,withLowK2_swap_mc]
  have mcB : measurementCount (branchBF760 L ext control)=measurementCount BF := withLowK2_swap_mc _ _ _ _ _ _
  have e0 : core760 L ext control=branchCK760 L ext control++branchBF760 L ext control++branchAF760 L ext control := rfl
  have e1 : ReflectionE1Low48Square.core L ext control=CK++BF++AF := rfl
  rw [e0,e1,run3,run3,mcC,mcB]
  have eqC := branchCK760_run_eq L hw ext control hn A B O hO s (records.take (measurementCount CK)) rfl sumB
    sumBound ho hp0 hc he hz
  rw [eqC]
  have rC := LowZero18Square.branchCK_correct L hw ext control hn A B O hO s (records.take (measurementCount CK))
    rfl sumB sumBound ho hp0 hc he hz
  generalize run CK (records.take (measurementCount CK)) s=t1 at rC ⊢
  have k1 := keepAll t1 rC.2.2
  have hO1 : regValue L.core.out t1.basis<SquareReduction.p := by rw [rC.2.1]; exact ofCast_lt _ _
  have eqB := branchBF760_run_eq L hw ext control hn B _ hO1 t1
    ((records.drop (measurementCount CK)).take (measurementCount BF)) k1.2.1 rfl k1.2.2.1 k1.2.2.2.2 he k1.2.2.2.1
  rw [eqB]
  have rB := LowZero18Square.branchBF_correct L hw ext control hn B _ hO1 t1
    ((records.drop (measurementCount CK)).take (measurementCount BF)) k1.2.1 rfl k1.2.2.1 k1.2.2.2.2 he k1.2.2.2.1
  generalize run BF ((records.drop (measurementCount CK)).take (measurementCount BF)) t1=t2 at rB ⊢
  have k2 := keepAll t2 (fun q hq => (rB.2.2 q hq).trans (rC.2.2 q hq))
  have hO2 : regValue L.core.out t2.basis<SquareReduction.p := by rw [rB.2.1]; exact ofCast_lt _ _
  exact branchAF760_run_eq L hw ext control hn A _ hO2 t2 _ k2.1 rfl k2.2.2.1 k2.2.2.2.2 he k2.2.2.2.1

section Final
open Secp256k1 CompressedPointDialog

theorem fastCore760_run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (hX : X<p)
    (s : State) (m : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    run (fastCore760 L) m s=run (ReflectionE1Low48Square.fastCore L) m s := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
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
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (OwnDiagAll12Square.kext_mem L hw q hq))
  have extOK:=OwnDiagAll12Square.kext_ok L hw hn
  have hext : ECDSAAdd.Entrant.ExtOK K L.core.generic (OwnDiagAll12Square.kext L) :=
    ⟨extOK.nodup,extOK.away,extOK.len⟩
  exact core760_run_eq K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean hext hz

private theorem pool_away_x' (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis resident hq

/-- **R2 square deliverable**: same hypotheses as `ReflectionE1Low48Square.boundary`. -/
theorem program760_run_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program760 L) m s=run (ReflectionE1Low48Square.program L) m s := by
  have core := fastCore760_run_eq L hw hn X.val Y.val X.isLt s m v.x v.y v.clean
  have result := ReflectionE1Low48Square.fastCore_boundary L hw hn X Y G origin s m v
  have clean : regValue L.dialogPool (run (ReflectionE1Low48Square.fastCore L) m s).basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x' L hn q hq)),v.clean]
  have eNew := ReflectionE1Square.place_run_eq L hw (fastCore760 L) s m v.clean (by rw [core]; exact clean)
  have eOld := ReflectionE1Square.place_run_eq L hw (ReflectionE1Low48Square.fastCore L) s m v.clean clean
  change run (program760 L) m s=run (fastCore760 L) m s at eNew
  change run (ReflectionE1Low48Square.program L) m s=run (ReflectionE1Low48Square.fastCore L) m s at eOld
  rw [eNew,eOld,core]

/-- The new square satisfies the old square's boundary verbatim. -/
theorem program760_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program760 L) m s).phase=s.phase ∧
    regValue L.point.x (run (program760 L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program760 L) m s).basis q=s.basis q := by
  rw [program760_run_eq L hw hn X Y G origin s m v]
  exact ReflectionE1Low48Square.boundary L hw hn X Y G origin s m v

end Final

end ECDSAAdd.Entrant.R2SqEp760

end -- R2 square


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end
