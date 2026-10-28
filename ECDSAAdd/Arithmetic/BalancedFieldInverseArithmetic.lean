import ECDSAAdd.Arithmetic.BalancedFieldInverseProgram
import ECDSAAdd.Arithmetic.MappedSources
import Mathlib.Tactic

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedField Secp256k1

private theorem complement_sub_cin (X Y N C : Nat) (hN : 0<N)
    (hX : X<N) (hY : Y<N) (hC : C≤1) :
    N-1-((X+(N-1-Y)+C)%N)=(Y+N-X-C)%N := by
  by_cases h : X+C≤Y
  · rw [Nat.mod_eq_of_lt (show X+(N-1-Y)+C<N by omega),
      show Y+N-X-C=(Y-X-C)+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show X+(N-1-Y)+C=(X+C-1-Y)+N by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (show X+C-1-Y<N by omega),Nat.mod_eq_of_lt (show Y+N-X-C<N by omega)]
    omega

/-- A measured-adder contract lifts through two fresh, measurement-free
complements. The carry-in may be either quantum basis value. -/
theorem complement_sandwich (ys : List Wire) (hn : ys.Nodup) (body : Program)
    (X C : Nat) (s : State) (m : List Bool) (hX : X<2^ys.length) (hC : C≤1)
    (hbody : let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
      (run body m u).phase=s.phase ∧
      (∀q,q∉ys → (run body m u).basis q=u.basis q) ∧
      regValue ys (run body m u).basis=(X+(2^ys.length-1-regValue ys s.basis)+C)%2^ys.length) :
    (run (notRegister ys++body++notRegister ys) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (notRegister ys++body++notRegister ys) m s).basis q=s.basis q) ∧
    regValue ys (run (notRegister ys++body++notRegister ys) m s).basis=
      (regValue ys s.basis+2^ys.length-X-C)%2^ys.length := by
  let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  let t := run body m u
  have first (ms : List Bool) : run (notRegister ys) ms s=u := notRegister_correct ys hn s ms
  have value : regValue ys (fun q => if q∈ys then !t.basis q else t.basis q)=
      2^ys.length-1-regValue ys t.basis := by
    rw [regValue_congr ys _ (fun q => !t.basis q) (by intro q hq; simp [hq]),regValue_complement]
  simp only [List.append_assoc,run_append,run_take,(notRegister_counts ys).2,List.drop_zero,first]
  rw [notRegister_correct ys hn]
  refine ⟨hbody.1,?_,?_⟩
  · intro q hq; simp only [hq,if_false]; exact (hbody.2.1 q hq).trans (by simp [hq])
  · rw [value,hbody.2.2]
    exact complement_sub_cin X (regValue ys s.basis) (2^ys.length) C
      (Nat.two_pow_pos _) hX (regValue_lt ys s.basis) hC

/-- Actual mapped subtraction, now proved for arbitrary carry-in. All
immutable selectors, cin and every carry restore, with all records allowed. -/
theorem mappedSub_any_correct (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (mappedSub bits ys carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (mappedSub bits ys carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (mappedSub bits ys carry cin) m s).basis=
      (regValue ys s.basis+2^ys.length-mappedValue bits s.basis-(s.basis cin).toNat)%2^ys.length := by
  have nd := List.nodup_append'.mp (List.nodup_cons.mp hn).2
  let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have awayCin : cin∉ys := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have clean : ∀q∈carry,u.basis q=false := by
    intro q hq; have away : q∉ys := fun h => List.disjoint_left.mp nd.2.2 h hq
    simp only [show u.basis q=s.basis q from by simp [u,away],hclean q hq]
  have source : mappedValue bits u.basis=mappedValue bits s.basis := by
    apply mappedValue_congr
    intro q hq; simp [u,show q∉ys from fun h => hs q hq (by simp [h])]
  have input : regValue ys u.basis=2^ys.length-1-regValue ys s.basis := by
    rw [regValue_congr ys _ (fun q => !s.basis q) (by intro q hq; simp [u,hq]),regValue_complement]
  have add := mappedAdd_correct bits ys carry cin hn hs hl hc u m clean
  apply complement_sandwich ys nd.1 (mappedAdd bits ys carry cin)
    (mappedValue bits s.basis) (s.basis cin).toNat s m
    (by simpa only [hl] using mappedValue_lt bits s.basis)
    (by cases s.basis cin <;> decide)
  simpa only [source,input,show u.basis cin=s.basis cin from by simp [u,awayCin]] using add

/-- The raw subtraction likewise supports its original sign carry-in,
without changing any source/control/workspace wire outside the target. -/
theorem subInPlace_any_correct (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::(xs++ys++carry)).Nodup) (hl : xs.length=ys.length)
    (hc : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) :
    (run (subInPlace xs ys carry cin) m s).phase=s.phase ∧
    (∀q,q∉ys → (run (subInPlace xs ys carry cin) m s).basis q=s.basis q) ∧
    regValue ys (run (subInPlace xs ys carry cin) m s).basis=
      (regValue ys s.basis+2^ys.length-regValue xs s.basis-(s.basis cin).toNat)%2^ys.length := by
  have words := List.nodup_cons.mp hn
  have split := List.nodup_append'.mp (show (xs++(ys++carry)).Nodup from by simpa only [List.append_assoc] using words.2)
  have nd := List.nodup_append'.mp split.2.1
  let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have ci : cin∉ys := fun h => words.1 (by simp [h])
  have clean : ∀q∈carry,u.basis q=false := by
    intro q hq; have away : q∉ys := fun h => List.disjoint_left.mp nd.2.2 h hq
    simp only [show u.basis q=s.basis q from by simp [u,away],hclean q hq]
  have source : regValue xs u.basis=regValue xs s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [u,show q∉ys from fun h => List.disjoint_left.mp split.2.2 hq (by simp [h])])
  have input : regValue ys u.basis=2^ys.length-1-regValue ys s.basis := by
    rw [regValue_congr ys _ (fun q => !s.basis q) (by intro q hq; simp [u,hq]),regValue_complement]
  have add := addInPlace_correct xs ys carry cin hn hl hc u m clean
  apply complement_sandwich ys nd.1 (addInPlace xs ys carry cin)
    (regValue xs s.basis) (s.basis cin).toNat s m
    (by simpa only [hl] using regValue_lt xs s.basis) (by cases s.basis cin <;> decide)
  simpa only [source,input,show u.basis cin=s.basis cin from by simp [u,ci]] using add

/-- Exact inverse field value; validity holds on the entire balanced domain. -/
def result (B : Bool) (R Y : Int) : Int := centerFp ((2*R-signedY B Y : Int) : Fp)

theorem result_bounds (B : Bool) (R Y : Int) : Centered (result B R Y) := centerFp_bounds _

theorem result_half (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    halfResult (rawSum B (result B R Y) Y)=R := by
  have hx := result_bounds B R Y
  have half := halfResult_center (rawSum B (result B R Y) Y) (rawSum_bounds B _ Y hx hy)
  have cast : (result B R Y : Fp)=((2*R-signedY B Y : Int) : Fp) := centerFp_cast _
  have eq : ((rawSum B (result B R Y) Y : Int) : Fp)/2=(R : Fp) := by
    simp only [rawSum,Int.cast_add,cast,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
    have two : (2 : Fp)≠0 := by decide
    field_simp [two]
    ring
  rw [half,eq,centerFp_of_center R hr]

end ECDSAAdd.Arithmetic.BalancedInverse

#print axioms ECDSAAdd.Arithmetic.BalancedInverse.mappedSub_any_correct
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.subInPlace_any_correct
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.result_half
