import ECDSAAdd.Arithmetic.MeasuredFoldKernel

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def copySlice (src word : List Wire) (shift : Nat) : Program :=
  copyRegister none src ((word.drop shift).take src.length)

/-- Zero padding is a property of the already clean word, so copying a
short shifted source needs no extra padding register. -/
theorem copySlice_zero_correct (src word : List Wire) (shift : Nat)
    (hn : (src++word).Nodup) (hl : shift+src.length≤word.length)
    (s : State) (records : List Bool) (hzero : regValue word s.basis=0) :
    (run (copySlice src word shift) records s).phase=s.phase ∧
    regValue word (run (copySlice src word shift) records s).basis=regValue src s.basis*2^shift ∧
    ∀q,q∉(word.drop shift).take src.length →
      (run (copySlice src word shift) records s).basis q=s.basis q := by
  let lo := word.take shift
  let dst := (word.drop shift).take src.length
  let hi := word.drop (shift+src.length)
  have len : dst.length=src.length := by simp [dst];omega
  have lowLen : lo.length=shift := by simp [lo];omega
  have split : word=lo++(dst++hi) := by
    have tail : word.drop shift=dst++hi := by
      simp [dst,hi,List.drop_drop,Nat.add_comm]
    calc
      word=lo++word.drop shift := (List.take_append_drop shift word).symm
      _=lo++(dst++hi) := by rw [tail]
  have nd : (src++dst).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have take := (List.take_sublist src.length (word.drop shift)).count_le q
    have drop := (List.drop_sublist shift word).count_le q
    simp only [List.count_append] at h ⊢
    dsimp only [dst]
    omega
  have wordNd : word.Nodup := (List.nodup_append'.mp hn).2.1
  have loAway (q : Wire) (hq : q∈lo) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp wordNd q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    rw [split] at h
    simp only [List.count_append] at h
    omega
  have hiAway (q : Wire) (hq : q∈hi) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp wordNd q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    rw [split] at h
    simp only [List.count_append] at h
    omega
  have dst0 : regValue dst s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hzero q
      (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  obtain ⟨phase,same,value⟩ := copyRegister_correct none src dst len.symm nd (by simp) s records
  have lo0 : regValue lo (run (copyRegister none src dst) records s).basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (same q (loAway q hq)).trans
      ((regValue_zero _ _).mp hzero q (List.mem_of_mem_take hq))
  have hi0 : regValue hi (run (copyRegister none src dst) records s).basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (same q (hiAway q hq)).trans
      ((regValue_zero _ _).mp hzero q (List.mem_of_mem_drop hq))
  refine ⟨phase,?_,same⟩
  change regValue word (run (copyRegister none src dst) records s).basis=_
  rw [split,regValue_append,regValue_append,lo0,hi0,value,dst0,lowLen]
  simp [copyValue,Nat.mul_comm]

end ECDSAAdd.Arithmetic
