import ECDSAAdd.Arithmetic.Paper935.FusedFoldArithmetic

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def foldTapPrefix (j : Nat) : List Wire := (List.range j).map (280+·)
def foldTapTarget (j : Nat) : List Wire := (List.range 25).map (280+j+·)
def foldTapSuffix (j : Nat) : List Wire :=
  (List.range (256-(j+25))).map (280+j+25+·)

theorem foldTap_split (j : Nat) (hj : j∈fusedFoldTaps) :
    fusedFoldWord=foldTapPrefix j++foldTapTarget j++foldTapSuffix j := by
  simp only [fusedFoldTaps,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem foldTap_geometry (j : Nat) (hj : j∈fusedFoldTaps) :
    (536::(fusedFoldHigh++[280+j+25])++foldTapTarget j).Nodup := by
  simp only [fusedFoldTaps,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

private theorem foldWord_nodup : fusedFoldWord.Nodup := by
  exact List.Nodup.map (f:=fun n : Nat => 280+n) (by intro a b h; exact Nat.add_left_cancel h) (List.nodup_range)

/-- A bound below the accumulator's padding bit forces that physical bit
zero. No dirty padding assumption is supplied by the caller. -/
theorem foldTap_pad_zero (j : Nat) (hj : j∈fusedFoldTaps) (s : BasisState)
    (small : regValue fusedFoldWord s<2^(j+25)) : s (280+j+25)=false := by
  have split : fusedFoldWord=foldTapPrefix (j+25)++(280+j+25)::
      ((List.range (256-(j+26))).map (280+j+26+·)) := by
    simp only [fusedFoldTaps,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rw [split,regValue_append] at small
  simp only [foldTapPrefix,List.length_map,List.length_range,regValue,List.foldr_cons] at small
  cases bit : s (280+j+25)
  · rfl
  · simp only [bit,if_true] at small
    simp only [Nat.mul_add,Nat.mul_one] at small
    omega

theorem fusedFoldTap_value (j : Nat) (hj : j∈fusedFoldTaps) (s : State) (m : List Bool)
    (carry : s.basis 536=false) (small : regValue fusedFoldWord s.basis<2^(j+24)) :
    regValue fusedFoldWord (run (fusedFoldTap j) m s).basis=
      regValue fusedFoldWord s.basis+2^j*regValue fusedFoldHigh s.basis := by
  have pad := foldTap_pad_zero j hj s.basis (by
    rw [show j+25=(j+24)+1 by omega,Nat.pow_succ]
    omega)
  have source : regValue (fusedFoldHigh++[280+j+25]) s.basis=regValue fusedFoldHigh s.basis := by
    simp [regValue,pad]
  have hbound : regValue fusedFoldHigh s.basis<2^24 := by
    have len : fusedFoldHigh.length=24 := by simp [fusedFoldHigh]
    simpa only [len] using regValue_lt fusedFoldHigh s.basis
  have decomposition : regValue fusedFoldWord s.basis=
      regValue (foldTapPrefix j) s.basis+2^j*(regValue (foldTapTarget j) s.basis+
        2^25*regValue (foldTapSuffix j) s.basis) := by
    rw [foldTap_split j hj,List.append_assoc,regValue_append,regValue_append]
    simp only [foldTapPrefix,foldTapTarget,List.length_map,List.length_range]
  have lower : 2^j*regValue (foldTapTarget j) s.basis≤regValue fusedFoldWord s.basis := by
    simp only [Nat.mul_add] at decomposition
    omega
  have target : regValue (foldTapTarget j) s.basis<2^24 := by
    by_contra bad
    have bound := (Nat.mul_le_mul_left (2^j) (Nat.le_of_not_gt bad)).trans lower
    rw [Nat.pow_add] at small
    omega
  have len : (fusedFoldHigh++[280+j+25]).length=(foldTapTarget j).length := by
    simp [fusedFoldHigh,foldTapTarget]
  have fits : regValue (foldTapTarget j) s.basis+
      regValue (fusedFoldHigh++[280+j+25]) s.basis<2^(foldTapTarget j).length := by
    rw [source]
    change regValue (foldTapTarget j) s.basis+regValue fusedFoldHigh s.basis<2^25
    omega
  have h := cuccaro_slice_value (foldTapPrefix j) (foldTapTarget j) (foldTapSuffix j)
    (fusedFoldHigh++[280+j+25]) 536 (foldTap_geometry j hj) len
    (by rw [←foldTap_split j hj]; exact foldWord_nodup) s m carry fits
  rw [←foldTap_split j hj,source] at h
  simpa only [foldTapPrefix,List.length_map,List.length_range] using h

theorem fusedFoldTap_frame (j : Nat) (hj : j∈fusedFoldTaps) (s : State) (m : List Bool) :
    (run (fusedFoldTap j) m s).phase=s.phase ∧
    ∀ q,q∉fusedFoldWord → (run (fusedFoldTap j) m s).basis q=s.basis q := by
  have h := cuccaroAdd_cin_frame 536 (fusedFoldHigh++[280+j+25]) (foldTapTarget j)
    (foldTap_geometry j hj) (by simp [fusedFoldHigh,foldTapTarget]) s.basis
    (s.basis 536) rfl (regValue (foldTapTarget j) s.basis) s m ⟨rfl,by intro q hq; rfl⟩
  refine ⟨h.1,?_⟩
  intro q outside
  apply h.2.2
  intro inside
  apply outside
  have subset : (foldTapTarget j).toFinset⊆fusedFoldWord.toFinset := by
    simp only [fusedFoldTaps,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  exact List.mem_toFinset.mp (subset (List.mem_toFinset.mpr inside))

end ECDSAAdd.Arithmetic.Paper935
