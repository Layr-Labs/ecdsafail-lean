import ECDSAAdd.Arithmetic.LiteralSkywalkSeedLayout

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- The copy restores every touched role outside its target word. -/
theorem literalSkywalkSeed_copy_stage (L : LiteralSkywalkSeedLayout) (hn : L.Valid)
    (hw : L.b.length=L.a.length) (A B : Nat) :
    Triple (LiteralSkywalkSeedValues L A B) (copyRegister none L.b L.a)
      (LiteralSkywalkSeedValues L (A ^^^ B) B) := by
  intro s m hin
  have h := copyRegister_correct none L.b L.a hw (L.copyND hn) (by simp) s m
  have keep (r : List Wire) (hr : r⊆[L.one,L.cin]++L.b++L.carry) :
      regValue r (run (copyRegister none L.b L.a) m s).basis=regValue r s.basis := by
    apply regValue_congr
    intro q hq
    exact h.2.1 q (L.outsideA hn q (hr hq))
  refine ⟨h.1,?_,(keep _ (by intro q hq; simp [hq])).trans hin.b,
    (keep _ (by intro q hq; simp [hq])).trans hin.carry,
    (h.2.1 _ (L.outsideA hn _ (by simp))).trans hin.cin,
    (h.2.1 _ (L.outsideA hn _ (by simp))).trans hin.one,
    (h.2.1 _ hn.orientationAway).trans hin.orientation⟩
  simpa only [hin.a,hin.b,copyValue] using h.2.2

/-- Exact forward literal arithmetic for every input word and record stream. -/
theorem literalSkywalkSeed_add_stage (L : LiteralSkywalkSeedLayout) (hn : L.Valid)
    (hc : L.carry.length+1=L.a.length) (A B k : Nat) :
    Triple (LiteralSkywalkSeedValues L A B) (literalConstAdd L.a L.carry L.cin L.one k)
      (LiteralSkywalkSeedValues L ((A+k)%2^L.a.length) B) := by
  intro s m hin
  have h := literalConstAdd_correct L.a L.carry L.cin L.one k (L.literalND hn) hc
    s m hin.one ((regValue_zero _ _).mp hin.carry)
  have keep (r : List Wire) (hr : r⊆[L.one,L.cin]++L.b++L.carry) :
      regValue r (run (literalConstAdd L.a L.carry L.cin L.one k) m s).basis=
        regValue r s.basis := by
    apply regValue_congr
    intro q hq
    exact h.2.1 q (L.outsideA hn q (hr hq))
  refine ⟨h.1,?_,(keep _ (by intro q hq; simp [hq])).trans hin.b,
    (keep _ (by intro q hq; simp [hq])).trans hin.carry,
    (h.2.1 _ (L.outsideA hn _ (by simp))).trans hin.cin,
    (h.2.1 _ (L.outsideA hn _ (by simp))).trans hin.one,
    (h.2.1 _ hn.orientationAway).trans hin.orientation⟩
  simpa only [hin.a,hin.cin,Bool.toNat_false,Nat.add_zero] using h.2.2

theorem literalSkywalkSeed_small_bounds (w p x : Nat) (hw : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) :
    p<2^w ∧ x<2^w ∧ p+x<2^(w-1) ∧ p+x<2^w := by
  have he : 2^(w-1)=2^(w-2)*2 := by
    rw [show w-1=(w-2)+1 by omega,pow_succ]
  have hm : 2^(w-1)≤2^w := Nat.pow_le_pow_right (by decide) (by omega)
  have hs : p+x<2^(w-1) := by rw [he]; omega
  exact ⟨by omega,by omega,hs,hs.trans_le hm⟩

/-- Positive exact seed, clean One/carry/Cin/orientation, unrestricted phase. -/
theorem literalSkywalkSeed_spec (L : LiteralSkywalkSeedLayout) (w p x : Nat)
    (hw : L.Widths w) (hn : L.Valid) (hw2 : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) :
    Triple (LiteralSkywalkSeedValues L 0 x) (literalSkywalkSeed L p)
      (LiteralSkywalkSeedValues L (p+x) x) := by
  have hb := literalSkywalkSeed_small_bounds w p x hw2 hp hx
  have c := literalSkywalkSeed_copy_stage L hn (hw.b.trans hw.a.symm) 0 x
  simp only [Nat.zero_xor] at c
  have a := literalSkywalkSeed_add_stage L hn (hw.carry.trans hw.a.symm) x x p
  rw [hw.a,Nat.add_comm x p,Nat.mod_eq_of_lt hb.2.2.2] at a
  exact c.seq a

/-- Exact independently measured unseed removes the literal then the copied B. -/
theorem literalSkywalkUnseed_spec (L : LiteralSkywalkSeedLayout) (w p x : Nat)
    (hw : L.Widths w) (hn : L.Valid) (hw2 : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) :
    Triple (LiteralSkywalkSeedValues L (p+x) x) (literalSkywalkUnseed L p)
      (LiteralSkywalkSeedValues L 0 x) := by
  have hb := literalSkywalkSeed_small_bounds w p x hw2 hp hx
  have a := literalSkywalkSeed_add_stage L hn (hw.carry.trans hw.a.symm)
    (p+x) x (2^L.a.length-p)
  rw [hw.a,show (p+x)+(2^w-p)=x+2^w by omega,Nat.add_mod_right,
    Nat.mod_eq_of_lt hb.2.1] at a
  have c := literalSkywalkSeed_copy_stage L hn (hw.b.trans hw.a.symm) x x
  simp only [Nat.xor_self] at c
  simpa only [literalSkywalkUnseed,hw.a] using a.seq c

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeed_spec
#print axioms ECDSAAdd.Arithmetic.literalSkywalkUnseed_spec
