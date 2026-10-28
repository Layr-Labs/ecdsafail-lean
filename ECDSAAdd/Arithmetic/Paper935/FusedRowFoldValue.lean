import ECDSAAdd.Arithmetic.Paper935.FusedFoldBuild
import ECDSAAdd.Framework.OutputFrame
import ECDSAAdd.Arithmetic.Paper935.FusedEndpointModel

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] fusedFoldBuild fusedFoldTap cuccaroAdd

private theorem low_bounds (q : Wire) (hq : q∈fusedFoldLow) : 24≤q ∧ q<280 := by
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp hq
  have hi := List.mem_range.mp hi
  dsimp only [Wire] at *
  omega

private theorem word_lower (q : Wire) (hq : q∈fusedFoldWord) : 280≤q := by
  obtain ⟨i,_,eq⟩ := List.mem_map.mp hq
  dsimp only [Wire] at *
  omega

private theorem build_disjoint_low : Disjoint fusedFoldLow.toFinset (wires fusedFoldBuild) := by
  have cp : Disjoint fusedFoldLow.toFinset
      (wires (copyRegister none fusedFoldHigh (fusedFoldWord.take 24))) := by
    apply Finset.disjoint_left.mpr
    intro q hq hw
    have bounds := low_bounds q (List.mem_toFinset.mp hq)
    rw [copyRegister_wires _ _ _ (by simp [fusedFoldHigh,fusedFoldWord])] at hw
    have empty : fusedFoldHigh.isEmpty=false := rfl
    simp only [empty,Bool.false_eq_true,if_false,Option.toList_none,List.nil_append,
      List.mem_toFinset,List.mem_append] at hw
    rcases hw with hh|hh
    · have upper : q<24 := List.mem_range.mp hh
      dsimp only [Wire] at *
      omega
    · have lower := word_lower q (List.mem_of_mem_take hh)
      dsimp only [Wire] at *
      omega
  have tap (j : Nat) (_hj : j∈fusedFoldTaps) : Disjoint fusedFoldLow.toFinset (wires (fusedFoldTap j)) := by
    apply Finset.disjoint_left.mpr
    intro q hq hw
    have bounds := low_bounds q (List.mem_toFinset.mp hq)
    rw [fusedFoldTap] at hw
    have support := cuccaroAdd_wires_subset (fusedFoldHigh++[280+j+25]) (foldTapTarget j) 536 hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at support
    rcases support with (rfl | hh | rfl) | ht
    · dsimp only [Wire] at *; omega
    · have upper : q<24 := List.mem_range.mp hh
      dsimp only [Wire] at *; omega
    · dsimp only [Wire] at *; omega
    · obtain ⟨i,_,eq⟩ := List.mem_map.mp ht
      dsimp only [Wire] at *; omega
  simp only [fusedFoldBuild,fusedFoldTaps,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    wires_append,Finset.disjoint_union_right]
  exact ⟨cp,⟨tap 4 (by decide),⟨tap 6 (by decide),⟨tap 7 (by decide),
    ⟨tap 8 (by decide),⟨tap 9 (by decide),tap 32 (by decide)⟩⟩⟩⟩⟩⟩

private theorem run_output (p : Program) (O : Finset Wire) (v : BasisState)
    (s : State) (m : List Bool) (dis : Disjoint O (wires p)) :
    run p m (withOutput O v s)=withOutput O v (run p m s) := by
  have h := runWithTape_withOutput (embedRecorded p) O v s m 0 (by simpa using dis)
  simpa only [runWithTape_embedRecorded,List.drop_zero] using h

private theorem low_outside_word (q : Wire) (hq : q∈fusedFoldLow) : q∉fusedFoldWord := by
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp hq
  have hi := List.mem_range.mp hi
  intro hw
  obtain ⟨j,hj,eqj⟩ := List.mem_map.mp hw
  have hj := List.mem_range.mp hj
  dsimp only [Wire] at *
  omega

/-- Compute/fold/uncompute with independent record lists. Only the low
word changes; all high bits, scratch and the carry root are restored. -/
theorem fusedRowFold_steps (s : State) (a b c : List Bool)
    (clean : regValue fusedFoldWord s.basis=0) (carry : s.basis 536=false) :
    let t := run fusedFoldBuild a s
    let u := run (cuccaroAdd fusedFoldWord fusedFoldLow 536) b t
    let out := run fusedFoldBuild.reverse c u
    out.phase=s.phase ∧ (∀q,q∉fusedFoldLow → out.basis q=s.basis q) ∧
    regValue fusedFoldLow out.basis=
      (regValue fusedFoldLow s.basis+(2^32+977)*regValue fusedFoldHigh s.basis)%2^256 := by
  let t := run fusedFoldBuild a s
  let u := run (cuccaroAdd fusedFoldWord fusedFoldLow 536) b t
  have build := fusedFoldBuild_value s a clean carry
  have cin : t.basis 536=false := (build.2.1 536 (by decide +kernel)).trans carry
  have low : regValue fusedFoldLow t.basis=regValue fusedFoldLow s.basis :=
    regValue_congr _ _ _ (fun q hq => build.2.1 q (low_outside_word q hq))
  have center := cuccaroAdd_cin_frame 536 fusedFoldWord fusedFoldLow (by decide +kernel)
    (by simp [fusedFoldWord,fusedFoldLow]) t.basis false cin (regValue fusedFoldLow t.basis)
    t b ⟨rfl,by intro q hq; rfl⟩
  have eq : u=withOutput fusedFoldLow.toFinset u.basis t := by
    apply State.extensionality
    · simpa only [withOutput] using center.1
    funext q
    by_cases hq : q∈fusedFoldLow
    · simp [withOutput,hq]
    · exact (center.2.2 q hq).trans (by simp [withOutput,hq])
  have undo : run fusedFoldBuild.reverse c u=withOutput fusedFoldLow.toFinset u.basis s := by
    calc
      run fusedFoldBuild.reverse c u =
          run fusedFoldBuild.reverse c (withOutput fusedFoldLow.toFinset u.basis t) := congrArg _ eq
      _ = withOutput fusedFoldLow.toFinset u.basis (run fusedFoldBuild.reverse c t) :=
        run_output _ _ _ _ c (by simpa [wires_reverse] using build_disjoint_low)
      _ = withOutput fusedFoldLow.toFinset u.basis s := by
        rw [run_reverse_proper _ fusedFoldBuild_proper s a c]
  change (run fusedFoldBuild.reverse c u).phase=s.phase ∧ _
  rw [undo]
  refine ⟨?_,?_,?_⟩
  · simp only [withOutput]
  · intro q hq
    simp [withOutput,hq]
  · have same : regValue fusedFoldLow (withOutput fusedFoldLow.toFinset u.basis s).basis=
        regValue fusedFoldLow u.basis := by
      apply regValue_congr
      intro q hq
      simp [withOutput,hq]
    rw [same,center.2.1,low,build.2.2]
    simp only [Bool.toNat_false,Nat.add_zero,fusedFoldLow,List.length_map,List.length_range]

theorem fusedRowFold_forward (s : State) (m : List Bool)
    (clean : regValue fusedFoldWord s.basis=0) (carry : s.basis 536=false) :
    let out := run (fusedRowFold false) m s
    out.phase=s.phase ∧ (∀q,q∉fusedFoldLow → out.basis q=s.basis q) ∧
    regValue fusedFoldLow out.basis=
      (regValue fusedFoldLow s.basis+(2^32+977)*regValue fusedFoldHigh s.basis)%2^256 := by
  have count := properProgram_measurementCount fusedFoldBuild fusedFoldBuild_proper
  simp only [fusedRowFold,Bool.false_eq_true,if_false,run_append,run_take]
  simp only [count,cuccaroAdd_measurementCount,measurementCount_append,Nat.zero_add,List.drop_zero]
  exact fusedRowFold_steps s m m m clean carry

/-- Actual source-order forward behavior, including wrap lanes. The full
frame proves restoration of every non-low-word bit, not only its value. -/
theorem fusedRowFoldSource_forward (s : State) (m : List Bool)
    (clean : regValue fusedFoldWord s.basis=0) (carry : s.basis 536=false) :
    let out := run (fusedRowFoldSource false) m s
    out.phase=s.phase ∧ (∀q,q∉fusedFoldLow → out.basis q=s.basis q) ∧
    regValue fusedFoldLow out.basis=
      (regValue fusedFoldLow s.basis+(2^32+977)*regValue fusedFoldHigh s.basis)%2^256 := by
  rw [fusedRowFoldSource_run]
  exact fusedRowFold_forward s m clean carry

theorem fusedRowFoldSource_cleanup (s : State) (m : List Bool)
    (clean : regValue fusedFoldWord s.basis=0) (carry : s.basis 536=false) :
    let out := run (fusedRowFoldSource false) m s
    regValue fusedFoldHigh out.basis=regValue fusedFoldHigh s.basis ∧
      regValue fusedFoldWord out.basis=0 ∧ out.basis 536=false := by
  have frame := (fusedRowFoldSource_forward s m clean carry).2.1
  refine ⟨?_,?_,?_⟩
  · apply regValue_congr
    intro q hq
    apply frame
    intro low
    have hb := low_bounds q low
    have upper : q<24 := List.mem_range.mp hq
    dsimp only [Wire] at *
    omega
  · rw [←clean]
    apply regValue_congr
    intro q hq
    apply frame
    intro low
    have hb := low_bounds q low
    have lower := word_lower q hq
    dsimp only [Wire] at *
    omega
  · exact (frame 536 (by decide +kernel)).trans carry

private theorem fold_magnitude (s : BasisState) :
    wideMagnitudeFold (regValue (fusedFoldLow++fusedFoldHigh) s)=
      regValue fusedFoldLow s+(2^32+977)*regValue fusedFoldHigh s := by
  have low : regValue fusedFoldLow s<2^256 := by
    have len : fusedFoldLow.length=256 := by simp [fusedFoldLow]
    simpa only [len] using regValue_lt fusedFoldLow s
  have len : fusedFoldLow.length=256 := by simp [fusedFoldLow]
  rw [wideMagnitudeFold,regValue_append,len,Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt low,Nat.add_mul_div_left _ _ (Nat.two_pow_pos 256),Nat.div_eq_of_lt low]
  simp only [Nat.zero_add,Nat.mul_comm]

/-- RowGood is sufficient for the actual source program's low output to
match the full mathematical magnitude fold. All cleanup remains unconditional. -/
theorem fusedRowFoldSource_of_good (call : FusedCall) (s : State) (m : List Bool)
    (clean : regValue fusedFoldWord s.basis=0) (carry : s.basis 536=false)
    (encoding : regValue (fusedFoldLow++fusedFoldHigh) s.basis=call.coefficient.natAbs)
    (good : call.RowGood) :
    regValue fusedFoldLow (run (fusedRowFoldSource false) m s).basis=
      wideMagnitudeFold call.coefficient.natAbs := by
  rw [(fusedRowFoldSource_forward s m clean carry).2.2,←fold_magnitude,encoding]
  exact Nat.mod_eq_of_lt good

end ECDSAAdd.Arithmetic.Paper935
