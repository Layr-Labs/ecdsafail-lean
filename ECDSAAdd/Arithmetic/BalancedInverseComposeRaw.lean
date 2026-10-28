import ECDSAAdd.Arithmetic.BalancedInverseComposeFold

set_option maxRecDepth 16384
set_option exponentiation.threshold 512
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

/-- The emitted source-complement/subtraction/source-complement stream
has the opposite signed direction, including arbitrary quantum carry-in. -/
theorem rawSubtract_modular (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hc : regValue L.carry s.basis=0) :
    (run (rawSubtract L) m s).phase=s.phase ∧
    (∀a,a∉rawTarget L → (run (rawSubtract L) m s).basis a=s.basis a) ∧
    regValue (rawTarget L) (run (rawSubtract L) m s).basis=
      signedWordValue 257 (!s.basis L.sign)
        (regValue (rawSource L) s.basis) (regValue (rawTarget L) s.basis) := by
  let xs := rawSource L
  let ys := rawTarget L
  have w := BalancedCircuit.widths L hw
  have xlen : xs.length=257 := by simpa only [xs] using w.1
  have ylen : ys.length=257 := by simpa only [ys] using w.2.1
  have nd := List.nodup_cons.mp (rawLayoutND L hn)
  have xd := List.nodup_append'.mp nd.2
  have xys := List.nodup_append'.mp xd.1
  have xa : L.sign∉xs := fun h => nd.1 (by simp [xs,h])
  have ya : L.sign∉ys := fun h => nd.1 (by simp [ys,h])
  have sourceND : xs.Nodup := xys.1
  have disjoint (a : Wire) (ha : a∈ys) : a∉xs :=
    fun h => List.disjoint_left.mp xys.2.2 h ha
  have carryAway (a : Wire) (ha : a∈L.carry) : a∉xs :=
    fun h => List.disjoint_left.mp xd.2.2 (List.mem_append_left _ h) ha
  let u := run (signComplement L.sign xs) m s
  have first := signComplement_correct L.sign xs sourceND xa s m
  change u.phase=s.phase ∧ (∀a,a∉xs → u.basis a=s.basis a) ∧
    regValue xs u.basis=(if s.basis L.sign then 2^xs.length-1-regValue xs s.basis
      else regValue xs s.basis) at first
  have sign1 : u.basis L.sign=s.basis L.sign := first.2.1 _ xa
  have target1 : regValue ys u.basis=regValue ys s.basis :=
    regValue_congr _ _ _ (fun a ha => first.2.1 a (disjoint a ha))
  have clean1 : ∀a∈L.carry,u.basis a=false :=
    fun a ha => (first.2.1 a (carryAway a ha)).trans ((regValue_zero _ _).mp hc a ha)
  let v := run (subInPlace xs ys L.carry L.sign) m u
  have second := subInPlace_any_correct xs ys L.carry L.sign (rawLayoutND L hn)
    (by omega) (by omega) u m clean1
  change v.phase=u.phase ∧ (∀a,a∉ys → v.basis a=u.basis a) ∧
    regValue ys v.basis=(regValue ys u.basis+2^ys.length-regValue xs u.basis-
      (u.basis L.sign).toNat)%2^ys.length at second
  have sign2 : v.basis L.sign=s.basis L.sign := (second.2.1 _ ya).trans sign1
  have source2 : regValue xs v.basis=regValue xs u.basis :=
    regValue_congr _ _ _ (fun a ha => second.2.1 a
      (fun h => List.disjoint_left.mp xys.2.2 ha h))
  let z := run (signComplement L.sign xs) (m.drop (measurementCount (subInPlace xs ys L.carry L.sign))) v
  have third := signComplement_correct L.sign xs sourceND xa v
    (m.drop (measurementCount (subInPlace xs ys L.carry L.sign)))
  change z.phase=v.phase ∧ (∀a,a∉xs → z.basis a=v.basis a) ∧
    regValue xs z.basis=(if v.basis L.sign then 2^xs.length-1-regValue xs v.basis
      else regValue xs v.basis) at third
  have source3 : regValue xs z.basis=regValue xs s.basis := by
    rw [third.2.2,sign2,source2,first.2.2]
    have h := regValue_lt xs s.basis
    cases s.basis L.sign <;> simp <;> omega
  have target3 : regValue ys z.basis=regValue ys v.basis :=
    regValue_congr _ _ _ (fun a ha => third.2.1 a (disjoint a ha))
  have eu : run (signComplement L.sign xs) m s=u := rfl
  have ev : run (subInPlace xs ys L.carry L.sign) m u=v := rfl
  have ez : run (signComplement L.sign xs)
      (m.drop (measurementCount (subInPlace xs ys L.carry L.sign))) v=z := rfl
  have actual : run (rawSubtract L) m s=z := by
    change run ((signComplement L.sign xs++subInPlace xs ys L.carry L.sign)++
      signComplement L.sign xs) m s=z
    rw [List.append_assoc,run_append,run_take,
      (signComplement_counts L.sign xs).2,List.drop_zero,eu,
      run_append,run_take,ev,ez]
  rw [actual]
  refine ⟨third.1.trans (second.1.trans first.1),?_,?_⟩
  · intro a ha
    by_cases hx : a∈xs
    · exact (regValue_eq_iff xs _ _).mp source3 a hx
    · exact (third.2.1 a hx).trans ((second.2.1 a ha).trans (first.2.1 a hx))
  · rw [target3,second.2.2,target1,first.2.2,sign1]
    have fit : regValue xs s.basis<2^257 := by
      simpa only [xlen] using regValue_lt xs s.basis
    rw [xlen,ylen]
    dsimp only [xs,ys] at fit ⊢
    cases hb : s.basis L.sign
    · simp [signedWordValue,hb]
    · simp only [hb,if_true,Bool.not_true,Bool.toNat_true,signedWordValue,Bool.false_eq_true,if_false]
      congr 1
      omega

/-- Exact inverse signed raw arithmetic on the entire centered domain. -/
theorem rawSubtract_signed (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (s : State) (m : List Bool)
    (hs : s.basis L.sign=B) (hy : signedRegValue (rawSource L) s.basis=Y)
    (ht : signedRegValue (rawTarget L) s.basis=rawSum B X Y)
    (hc : regValue L.carry s.basis=0) :
    (run (rawSubtract L) m s).phase=s.phase ∧
    signedRegValue (rawTarget L) (run (rawSubtract L) m s).basis=X ∧
    ∀a,a∉rawTarget L → (run (rawSubtract L) m s).basis a=s.basis a := by
  have h := rawSubtract_modular L hw hn s m hc
  have w := BalancedCircuit.widths L hw
  have source : signedDecode 257 (regValue (rawSource L) s.basis)=Y := by
    simpa [signedRegValue,w.1] using hy
  have target : signedDecode 257 (regValue (rawTarget L) s.basis)=rawSum B X Y := by
    simpa [signedRegValue,w.2.1] using ht
  have direction : signedIntegerValue (!B) Y (rawSum B X Y)=X := by
    cases B <;> simp [signedIntegerValue,rawSum,signedY]
  have bound : -((2^(257-1) : Nat) : Int)≤X ∧ X<((2^(257-1) : Nat) : Int) := by
    have constants := BalancedField.constants
    unfold Centered at hx
    norm_num at ⊢
    omega
  have lift := signedWordValue_lift 257 (!B)
    (regValue (rawSource L) s.basis) (regValue (rawTarget L) s.basis)
    (by omega) (by simpa only [w.1] using regValue_lt (rawSource L) s.basis)
    (by rw [source,target,direction]; exact bound.1)
    (by rw [source,target,direction]; exact bound.2)
  rw [source,target,direction] at lift
  refine ⟨h.1,?_,h.2.1⟩
  unfold signedRegValue
  rw [w.2.1,h.2.2,hs]
  exact lift

end ECDSAAdd.Arithmetic.BalancedInverse

#print axioms ECDSAAdd.Arithmetic.BalancedInverse.rawSubtract_modular
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.rawSubtract_signed
