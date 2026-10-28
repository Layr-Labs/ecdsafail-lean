import ECDSAAdd.Arithmetic.DirectZeroDivisor

namespace ECDSAAdd.Arithmetic

/-- Zero repair around a numerator-only kernel, without a backup divisor. -/
def directZeroControlled (xs carry : List Wire) (cin flag : Wire) (kernel : Program) : Program :=
  directZeroDivisorEnter xs carry cin flag ++
    (kernel ++ directZeroDivisorLeave xs carry cin flag)

/-- The kernel contract includes its true caller frame, rather than merely
requiring a numerically correct numerator. Independent records are allowed. -/
theorem directZeroControlled_states (xs ys carry : List Wire) (cin flag : Wire)
    (hn : (flag::cin::(xs++carry++ys)).Nodup)
    (hc : carry.length+1=xs.length) (kernel : Program) (s : State)
    (enterRecord kernelRecord leaveRecord : List Bool) (R : Nat)
    (hcin : s.basis cin=false) (hflag : s.basis flag=false)
    (hclean : ∀ q∈carry,s.basis q=false)
    (hkernel : ∀ (t : State) (ms : List Bool),
      regValue xs t.basis=directDivisor (regValue xs s.basis) →
      regValue ys t.basis=regValue ys s.basis →
      t.basis flag=decide (regValue xs s.basis=0) →
      (∀ q,q≠flag → q∉xs → t.basis q=s.basis q) →
      (run kernel ms t).phase=t.phase ∧ regValue ys (run kernel ms t).basis=R ∧
        ∀ q,q∉ys → (run kernel ms t).basis q=t.basis q) :
    let t := run (directZeroDivisorEnter xs carry cin flag) enterRecord s
    let u := run kernel kernelRecord t
    let v := run (directZeroDivisorLeave xs carry cin flag) leaveRecord u
    v.phase=s.phase ∧ regValue ys v.basis=R ∧
      ∀ q,q∉ys → v.basis q=s.basis q := by
  dsimp only
  have hn0 : (flag::cin::(xs++carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at hh ⊢
    omega
  have hdis : xs.Disjoint ys := by
    apply List.disjoint_left.mpr
    intro q hx hy
    have hh := List.nodup_iff_count.mp hn q
    have hp := List.count_pos_iff.mpr hx
    have hq := List.count_pos_iff.mpr hy
    simp only [List.count_cons,List.count_append] at hh
    omega
  have flagAway : flag∉ys := by
    intro h; exact (List.nodup_cons.mp hn).1 (by simp [h])
  have cinAway : cin∉ys := by
    intro h; exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [h])
  have carryAway (q : Wire) (hq : q∈carry) : q∉ys := by
    intro hy
    have hh := List.nodup_iff_count.mp hn q
    have hp := List.count_pos_iff.mpr hq
    have hj := List.count_pos_iff.mpr hy
    simp only [List.count_cons,List.count_append] at hh
    omega
  let t := run (directZeroDivisorEnter xs carry cin flag) enterRecord s
  let u := run kernel kernelRecord t
  let v := run (directZeroDivisorLeave xs carry cin flag) leaveRecord u
  have he := directZeroDivisorEnter_correct xs carry cin flag hn0 hc s enterRecord hcin hflag hclean
  have hy : regValue ys t.basis=regValue ys s.basis := by
    apply regValue_congr
    intro q hq
    exact he.2.1 q (fun h => flagAway (h ▸ hq))
      (fun hx => List.disjoint_left.mp hdis hx hq)
  have hk := hkernel t kernelRecord he.2.2.2.1 hy he.2.2.1 he.2.1
  have huFlag : u.basis flag=decide (regValue xs s.basis=0) :=
    (hk.2.2 flag flagAway).trans he.2.2.1
  have huX : regValue xs u.basis=directDivisor (regValue xs s.basis) := by
    exact (regValue_congr xs _ _ (fun q hq => hk.2.2 q
      (fun hy => List.disjoint_left.mp hdis hq hy))).trans he.2.2.2.1
  have huCin : u.basis cin=false := (hk.2.2 cin cinAway).trans he.2.2.2.2.1
  have huCarry : ∀ q∈carry,u.basis q=false := by
    intro q hq; exact (hk.2.2 q (carryAway q hq)).trans (he.2.2.2.2.2 q hq)
  have hl := directZeroDivisorLeave_correct xs carry cin flag hn0 hc
    (regValue xs s.basis) u leaveRecord huCin huFlag huX huCarry
  have hword := directZeroDivisorLeave_restores_word xs carry cin flag hn0 hc
    s u leaveRecord huCin huFlag huX huCarry
  refine ⟨hl.1.trans (hk.1.trans he.1),?_,?_⟩
  · exact (regValue_congr ys _ _ (fun q hq => hl.2.1 q
      (fun h => flagAway (h ▸ hq))
      (fun hx => List.disjoint_left.mp hdis hx hq))).trans hk.2.1
  · intro q hqy
    by_cases hq : q=flag
    · subst q; exact hl.2.2.1.trans hflag.symm
    by_cases hx : q∈xs
    · exact hword q hx
    · exact (hl.2.1 q hq hx).trans ((hk.2.2 q hqy).trans (he.2.1 q hq hx))

/-- Exact emitted cost of the complete zero-repair wrapper. -/
theorem directZeroControlled_counts (xs carry : List Wire) (cin flag : Wire) (kernel : Program)
    (hc : carry.length+1=xs.length) :
    toffoliCount (directZeroControlled xs carry cin flag kernel)=toffoliCount kernel+2*(xs.length-1) ∧
    measurementCount (directZeroControlled xs carry cin flag kernel)=
      measurementCount kernel+2*(xs.length-2) := by
  have h := directZeroDivisor_counts xs carry cin flag hc
  simp only [directZeroControlled,toffoliCount_append,measurementCount_append,
    h.1,h.2.1,h.2.2.1,h.2.2.2]
  omega

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.directZeroControlled_states
#print axioms ECDSAAdd.Arithmetic.directZeroControlled_counts
