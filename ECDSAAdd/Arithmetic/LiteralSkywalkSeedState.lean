import ECDSAAdd.Arithmetic.LiteralSkywalkSeedProof

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- The bank-free seed has the same positive Stein encoding. -/
def literalSkywalkSeedRead (L : LiteralSkywalkSeedLayout) (s : BasisState) : SkywalkRails.State :=
  ⟨signedRegValue L.a s,signedRegValue L.b s,s L.orientation⟩

theorem literalSkywalkSeed_encode (L : LiteralSkywalkSeedLayout) (w p x : Nat)
    (hw : L.Widths w) (hw2 : 2≤w) (hp : p<2^(w-2)) (hx : x<2^(w-2))
    (s : BasisState) (hs : LiteralSkywalkSeedValues L (p+x) x s) :
    literalSkywalkSeedRead L s=SkywalkRails.encode false false
      ((SkywalkNat.init x p).u:Int) ((SkywalkNat.init x p).v:Int) := by
  have hb := literalSkywalkSeed_small_bounds w p x hw2 hp hx
  have hxsign : x<2^(w-1) := by omega
  have ha : signedRegValue L.a s=(p+x:Int) := by
    unfold signedRegValue signedDecode
    rw [hw.a,hs.a]
    simp [hb.2.2.1]
  have hbs : signedRegValue L.b s=(x:Int) := by
    unfold signedRegValue signedDecode
    rw [hw.b,hs.b]
    simp [hxsign]
  simp only [literalSkywalkSeedRead,ha,hbs,hs.orientation,SkywalkNat.init,
    SkywalkRails.encode,SkywalkRails.signed,Bool.false_eq_true,if_false]
  congr 1
  omega

/-- Full phase and basis roundtrip with independent arbitrary seed/unseed records. -/
theorem literalSkywalkSeed_roundtrip (L : LiteralSkywalkSeedLayout) (w p x : Nat)
    (hw : L.Widths w) (hn : L.Valid) (hw2 : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) (s : State) (m1 m2 : List Bool)
    (hin : LiteralSkywalkSeedValues L 0 x s.basis) :
    run (literalSkywalkUnseed L p) m2 (run (literalSkywalkSeed L p) m1 s)=s := by
  let t := run (literalSkywalkSeed L p) m1 s
  let u := run (literalSkywalkUnseed L p) m2 t
  obtain ⟨hp1,ht⟩ := literalSkywalkSeed_spec L w p x hw hn hw2 hp hx s m1 hin
  obtain ⟨hp2,hu⟩ := literalSkywalkUnseed_spec L w p x hw hn hw2 hp hx t m2 ht
  have ha : ∀q∈L.a,u.basis q=s.basis q :=
    (regValue_eq_iff _ _ _).mp (hu.a.trans hin.a.symm)
  have hb : ∀q∈L.b,u.basis q=s.basis q :=
    (regValue_eq_iff _ _ _).mp (hu.b.trans hin.b.symm)
  have hc : ∀q∈L.carry,u.basis q=s.basis q :=
    (regValue_eq_iff _ _ _).mp (hu.carry.trans hin.carry.symm)
  change u=s
  apply congrArg₂ State.mk
  · exact hp2.trans hp1
  · funext q
    by_cases he : q=L.one
    · subst q
      exact hu.one.trans hin.one.symm
    by_cases he : q=L.cin
    · subst q
      exact hu.cin.trans hin.cin.symm
    by_cases hqa : q∈L.a
    · exact ha q hqa
    by_cases hqb : q∈L.b
    · exact hb q hqb
    by_cases hqc : q∈L.carry
    · exact hc q hqc
    have hout : q∉L.usedWires := by
      simp only [LiteralSkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append]
      tauto
    exact (literalSkywalkSeed_frame L w p hw t m2 q hout).2.trans
      (literalSkywalkSeed_frame L w p hw s m1 q hout).1

/-- The seed restores every site outside A, including all its touched scratch. -/
theorem literalSkywalkSeed_preserves_outsideA (L : LiteralSkywalkSeedLayout) (w p x : Nat)
    (hw : L.Widths w) (hn : L.Valid) (hw2 : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues L 0 x s.basis) (q : Wire) (hqa : q∉L.a) :
    (run (literalSkywalkSeed L p) m s).basis q=s.basis q := by
  obtain ⟨_,hout⟩ := literalSkywalkSeed_spec L w p x hw hn hw2 hp hx s m hin
  by_cases he : q=L.one
  · subst q
    exact hout.one.trans hin.one.symm
  by_cases he : q=L.cin
  · subst q
    exact hout.cin.trans hin.cin.symm
  by_cases hqb : q∈L.b
  · exact (regValue_eq_iff _ _ _).mp (hout.b.trans hin.b.symm) q hqb
  by_cases hqc : q∈L.carry
  · exact (regValue_eq_iff _ _ _).mp (hout.carry.trans hin.carry.symm) q hqc
  have hu : q∉L.usedWires := by
    simp only [LiteralSkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append]
    tauto
  exact (literalSkywalkSeed_frame L w p hw s m q hu).1

/-- The independently emitted unseed has the same complete outsider frame. -/
theorem literalSkywalkUnseed_preserves_outsideA (L : LiteralSkywalkSeedLayout) (w p x : Nat)
    (hw : L.Widths w) (hn : L.Valid) (hw2 : 2≤w)
    (hp : p<2^(w-2)) (hx : x<2^(w-2)) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues L (p+x) x s.basis) (q : Wire) (hqa : q∉L.a) :
    (run (literalSkywalkUnseed L p) m s).basis q=s.basis q := by
  obtain ⟨_,hout⟩ := literalSkywalkUnseed_spec L w p x hw hn hw2 hp hx s m hin
  by_cases he : q=L.one
  · subst q
    exact hout.one.trans hin.one.symm
  by_cases he : q=L.cin
  · subst q
    exact hout.cin.trans hin.cin.symm
  by_cases hqb : q∈L.b
  · exact (regValue_eq_iff _ _ _).mp (hout.b.trans hin.b.symm) q hqb
  by_cases hqc : q∈L.carry
  · exact (regValue_eq_iff _ _ _).mp (hout.carry.trans hin.carry.symm) q hqc
  have hu : q∉L.usedWires := by
    simp only [LiteralSkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append]
    tauto
  exact (literalSkywalkSeed_frame L w p hw s m q hu).2

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeed_encode
#print axioms ECDSAAdd.Arithmetic.literalSkywalkSeed_roundtrip
#print axioms ECDSAAdd.Arithmetic.literalSkywalkUnseed_preserves_outsideA
