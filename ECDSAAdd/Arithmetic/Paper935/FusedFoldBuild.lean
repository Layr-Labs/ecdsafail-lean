import ECDSAAdd.Arithmetic.Paper935.FusedFoldTap

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] fusedFoldTap

def FoldTapPlan : Nat → List Nat → Prop
  | _,[] => True
  | part,j::rest => j∈fusedFoldTaps ∧ part<2^j ∧ FoldTapPlan (part+2^j) rest

theorem fusedFoldTaps_plan : FoldTapPlan 1 fusedFoldTaps := by norm_num [FoldTapPlan,fusedFoldTaps]

private theorem high_outside (q : Wire) (hq : q∈fusedFoldHigh) : q∉fusedFoldWord := by
  simp only [fusedFoldHigh,List.mem_range] at hq
  intro hw
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp hw
  have hi := List.mem_range.mp hi
  dsimp only [Wire] at *
  omega

private theorem carry_outside : (536 : Wire)∉fusedFoldWord := by
  intro hw
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp hw
  have hi := List.mem_range.mp hi
  dsimp only [Wire] at *
  omega

/-- The running coefficient bound ensures every actual tap sees clean
padding and a nonoverflowing 25-bit accumulator. -/
theorem fusedFoldTap_chain (js : List Nat) (part H : Nat) (plan : FoldTapPlan part js)
    (s : State) (m : List Bool) (high : regValue fusedFoldHigh s.basis=H)
    (word : regValue fusedFoldWord s.basis=part*H) (carry : s.basis 536=false) :
    let out := run (js.flatMap fusedFoldTap) m s
    out.phase=s.phase ∧ (∀q,q∉fusedFoldWord → out.basis q=s.basis q) ∧
      regValue fusedFoldWord out.basis=(part+(js.map (2^·)).sum)*H := by
  induction js generalizing part s m with
  | nil => simp [run,word]
  | cons j rest ih =>
    obtain ⟨member,bound,nextPlan⟩ := plan
    have hH : H<2^24 := by
      have len : fusedFoldHigh.length=24 := by simp [fusedFoldHigh]
      simpa only [len,high] using regValue_lt fusedFoldHigh s.basis
    have small : regValue fusedFoldWord s.basis<2^(j+24) := by
      rw [word,Nat.pow_add]
      exact (Nat.mul_le_mul_right H (Nat.le_of_lt bound)).trans_lt
        (Nat.mul_lt_mul_of_pos_left hH (Nat.two_pow_pos j))
    let t := run (fusedFoldTap j) m s
    have frame := fusedFoldTap_frame j member s m
    have nextHigh : regValue fusedFoldHigh t.basis=H := by
      rw [←high]
      exact regValue_congr _ _ _ (fun q hq => frame.2 q (high_outside q hq))
    have nextWord : regValue fusedFoldWord t.basis=(part+2^j)*H := by
      rw [fusedFoldTap_value j member s m carry small,word,high]
      ring
    have nextCarry : t.basis 536=false := (frame.2 536 carry_outside).trans carry
    have tailResult := ih (part+2^j) nextPlan t (m.drop (measurementCount (fusedFoldTap j)))
      nextHigh nextWord nextCarry
    simp only [List.flatMap_cons,run_append,run_take]
    refine ⟨tailResult.1.trans frame.1,?_,?_⟩
    · intro q hq
      exact (tailResult.2.1 q hq).trans (frame.2 q hq)
    · simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using tailResult.2.2

/-- The initial tap copies the high payload into the clean borrowed word.
The uncopied suffix remains zero by the physical frame. -/
theorem fusedFoldCopy_value (s : State) (m : List Bool) (clean : regValue fusedFoldWord s.basis=0) :
    let out := run (copyRegister none fusedFoldHigh (fusedFoldWord.take 24)) m s
    out.phase=s.phase ∧ (∀q,q∉fusedFoldWord → out.basis q=s.basis q) ∧
      regValue fusedFoldWord out.basis=regValue fusedFoldHigh s.basis := by
  have copied := copyRegister_correct none fusedFoldHigh (fusedFoldWord.take 24)
    (by simp [fusedFoldHigh,fusedFoldWord]) (by decide) (by simp) s m
  have lowZero : regValue (fusedFoldWord.take 24) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp clean q (List.mem_of_mem_take hq))
  have low := copied.2.2
  simp only [lowZero,copyValue,Nat.zero_xor] at low
  have suffixZero : regValue (fusedFoldWord.drop 24)
      (run (copyRegister none fusedFoldHigh (fusedFoldWord.take 24)) m s).basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    rw [copied.2.1 q (by
      have dis : Disjoint (fusedFoldWord.drop 24).toFinset (fusedFoldWord.take 24).toFinset := by decide +kernel
      intro hd
      exact Finset.disjoint_left.mp dis (List.mem_toFinset.mpr hq) (List.mem_toFinset.mpr hd))]
    exact (regValue_zero _ _).mp clean q (List.mem_of_mem_drop hq)
  refine ⟨copied.1,?_,?_⟩
  · intro q hq
    exact copied.2.1 q (fun mem => hq (List.mem_of_mem_take mem))
  · have split := regValue_append (fusedFoldWord.take 24) (fusedFoldWord.drop 24)
      (run (copyRegister none fusedFoldHigh (fusedFoldWord.take 24)) m s).basis
    rw [List.take_append_drop,low,suffixZero] at split
    simpa using split

/-- Complete tap accumulator: high*(2^32+977), with every non-word bit and
phase restored. The operand-padding invariants are derived, not assumed. -/
theorem fusedFoldBuild_value (s : State) (m : List Bool)
    (clean : regValue fusedFoldWord s.basis=0) (carry : s.basis 536=false) :
    let out := run fusedFoldBuild m s
    out.phase=s.phase ∧ (∀q,q∉fusedFoldWord → out.basis q=s.basis q) ∧
      regValue fusedFoldWord out.basis=(2^32+977)*regValue fusedFoldHigh s.basis := by
  let t := run (copyRegister none fusedFoldHigh (fusedFoldWord.take 24)) m s
  have copied := fusedFoldCopy_value s m clean
  have high : regValue fusedFoldHigh t.basis=regValue fusedFoldHigh s.basis :=
    regValue_congr _ _ _ (fun q hq => copied.2.1 q (high_outside q hq))
  have hc : t.basis 536=false := (copied.2.1 536 carry_outside).trans carry
  have tailResult := fusedFoldTap_chain fusedFoldTaps 1 (regValue fusedFoldHigh s.basis)
    fusedFoldTaps_plan t (m.drop (measurementCount (copyRegister none fusedFoldHigh (fusedFoldWord.take 24))))
    high (by simpa only [Nat.one_mul] using copied.2.2) hc
  simp only [fusedFoldBuild,run_append,run_take]
  refine ⟨tailResult.1.trans copied.1,?_,?_⟩
  · intro q hq
    exact (tailResult.2.1 q hq).trans (copied.2.1 q hq)
  · have coeff : 1+(fusedFoldTaps.map (2^·)).sum=2^32+977 := by decide
    simpa only [coeff] using tailResult.2.2

end ECDSAAdd.Arithmetic.Paper935
