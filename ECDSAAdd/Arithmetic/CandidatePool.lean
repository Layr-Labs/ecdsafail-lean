import ECDSAAdd.Arithmetic.InversePorts

namespace ECDSAAdd.Arithmetic

/-- 求逆八线银行的实际七线支持；旧 out 在偏移5。 -/
private def usedBank (w : Nat → Wire) (a : Nat) : List Wire :=
  [w a,w (a+1),w (a+2),w (a+3),w (a+4),w (a+6),w (a+7)]

private theorem usedBank_sublist (w : Nat → Wire) (a : Nat) :
    (usedBank w a).Sublist (wireBlock w a 8) := by
  simp only [usedBank,wireBlock,List.range',List.map_cons,List.map_nil]
  exact (((((List.Sublist.refl _).cons _).cons₂ _).cons₂ _).cons₂ _).cons₂ _ |>.cons₂ _

/-- 模减使用前1827位，补回求逆前228个银行的旧out；余29个out仍不触及。 -/
def candidatePool (w : Nat → Wire) : List Wire :=
  wireBlock w 0 1829 ++ (List.range 29).flatMap (fun i => usedBank w (1829+8*i)) ++
    (wireBlock w 2061 41 ++ (w 2102 :: (List.range 512).map (fun i => w (2103+2*i))) ++ wireBlock w 3126 30 ++ wireBlock w 5698 1)

theorem candidatePool_length (w : Nat → Wire) : (candidatePool w).length=2617 := by
  have hh (is : List Nat) : (is.flatMap (fun i => usedBank w (1829+8*i))).length=7*is.length := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      rw [List.flatMap_cons,List.length_append,ih]
      change 7+7*is.length=7*(is.length+1)
      omega
  simp [candidatePool,hh,wireBlock_length]

theorem candidatePool_sublist (w : Nat → Wire) : (candidatePool w).Sublist (wireBlock w 0 5699) := by
  have hm := List.Sublist.flatMap_right (List.range 29) (fun i _ => usedBank_sublist w (1829+8*i))
  rw [wireBlock_flatMap] at hm
  have recs : (w 2102 :: (List.range 512).map (fun i => w (2103+2*i))).Sublist (wireBlock w 2102 1024) := by
    let rs := (List.range 512).map (fun i => (⟨w (2102+2*i),w (2102+2*i+1)⟩ : RoundRecord))
    have h := oneBitRecordWires_sublist rs
    have hr : oneBitRecordWires rs = w 2102 :: (List.range 512).map (fun i => w (2103+2*i)) := by
      unfold rs
      rw [oneBitRecordWires_range (n:=511)]
      simp only [Nat.mul_zero,Nat.add_zero]
      apply congrArg (List.cons (w 2102))
      apply List.map_congr_left
      intro i _
      congr 1
      omega
    have hb : rs.flatMap RoundRecord.wires=wireBlock w 2102 1024 := by
      simp only [rs,List.flatMap_map,RoundRecord.wires]
      change ((List.range 512).flatMap (fun i => wireBlock w (2102+2*i) 2))=_
      exact wireBlock_flatMap _ _ _ _
    rwa [hr,hb] at h
  have tail : (wireBlock w 2061 41 ++ (w 2102 :: (List.range 512).map (fun i => w (2103+2*i))) ++ wireBlock w 3126 30 ++ wireBlock w 5698 1).Sublist (wireBlock w 2061 3638) := by
    have hh := (recs.append_left (wireBlock w 2061 41)).append_right (wireBlock w 3126 30)
    rw [wireBlock_append w 2061 41 1024,wireBlock_append w 2061 1065 30] at hh
    have he : wireBlock w 2061 1095++wireBlock w 3156 2542++wireBlock w 5698 1=wireBlock w 2061 3638 := by
      rw [wireBlock_append w 2061 1095 2542,wireBlock_append w 2061 3637 1]
    rw [←he]
    exact (hh.trans (List.sublist_append_left _ _)).append_right _
  have hh := (hm.append_left (wireBlock w 0 1829)).append tail
  rw [wireBlock_append w 0 1829 232,wireBlock_append w 0 2061 3638] at hh
  exact hh

private theorem block_prefix (w : Nat → Wire) (a b : Nat) (h : a≤b) :
    (wireBlock w 0 a).Sublist (wireBlock w 0 b) := by
  have hh : wireBlock w 0 a++wireBlock w a (b-a)=wireBlock w 0 b := by
    simpa only [Nat.zero_add,Nat.add_sub_of_le h] using wireBlock_append w 0 a (b-a)
  rw [← hh]
  exact List.sublist_append_left _ _

private theorem bank_prefix (w : Nat → Wire) (i : Nat) (hi : i<228) :
    ∀ q∈usedBank w (5+8*i), q∈wireBlock w 0 1829 := by
  intro q hq
  have hm := (usedBank_sublist w (5+8*i)).subset hq
  simp only [wireBlock,List.mem_map,List.mem_range'_1] at hm ⊢
  obtain ⟨j,⟨hj1,hj2⟩,rfl⟩ := hm
  exact ⟨j,⟨by omega,by omega⟩,rfl⟩

theorem candidatePool_union (w : Nat → Wire) :
    (candidatePool w).toFinset=(wireBlock w 0 1827).toFinset ∪ (poolInverseUsedWork w).toFinset := by
  have hi : poolInverseUsedWork w=wireBlock w 0 5++
      (List.range 257).flatMap (fun i => usedBank w (5+8*i))++(wireBlock w 2061 41 ++ (w 2102 :: (List.range 512).map (fun i => w (2103+2*i))) ++ wireBlock w 3126 30 ++ wireBlock w 5698 1) := by
    simp only [poolInverseUsedWork,List.append_assoc]
    apply congrArg (fun xs => wireBlock w 0 5 ++ xs ++ (wireBlock w 2061 41 ++ ((w 2102 :: (List.range 512).map (fun i => w (2103+2*i))) ++ (wireBlock w 3126 30 ++ wireBlock w 5698 1))))
    apply congrArg (fun f => (List.range 257).flatMap f)
    funext i
    rfl
  ext q
  simp only [candidatePool,hi,List.mem_toFinset,Finset.mem_union,List.mem_append]
  constructor
  · rintro ((hq|hq)|hq)
    · simp only [wireBlock,List.mem_map,List.mem_range'_1] at hq
      obtain ⟨i,⟨_,hi⟩,rfl⟩ := hq
      by_cases hb : i<1827
      · left
        simp only [wireBlock,List.mem_map,List.mem_range'_1]
        exact ⟨i,⟨by omega,hb⟩,rfl⟩
      · right; left; right
        apply List.mem_flatMap.mpr
        refine ⟨227,by simp,?_⟩
        have he : i=1827 ∨ i=1828 := by omega
        rcases he with rfl|rfl <;> simp [usedBank]
    · obtain ⟨i,hi,hq⟩ := List.mem_flatMap.mp hq
      have hlt : i<29 := List.mem_range.mp hi
      right; left; right
      apply List.mem_flatMap.mpr
      refine ⟨i+228,List.mem_range.mpr (by omega),?_⟩
      have he : 5+8*(i+228)=1829+8*i := by omega
      simpa only [he] using hq
    · exact Or.inr (Or.inr hq)
  · rintro (hq|((hq|hq)|hq))
    · exact Or.inl (Or.inl ((block_prefix w 1827 1829 (by omega)).subset hq))
    · exact Or.inl (Or.inl ((block_prefix w 5 1829 (by omega)).subset hq))
    · obtain ⟨i,hi,hq⟩ := List.mem_flatMap.mp hq
      have hlt := List.mem_range.mp hi
      by_cases hb : i<228
      · exact Or.inl (Or.inl (bank_prefix w i hb q hq))
      · left; right
        apply List.mem_flatMap.mpr
        refine ⟨i-228,List.mem_range.mpr (by omega),?_⟩
        have he : 1829+8*(i-228)=5+8*i := by omega
        simpa only [he] using hq
    · exact Or.inr hq

end ECDSAAdd.Arithmetic
