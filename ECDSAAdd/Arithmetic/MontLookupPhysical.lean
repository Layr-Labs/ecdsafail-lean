import ECDSAAdd.Arithmetic.MontArithmeticPhysical

namespace ECDSAAdd.Arithmetic

/-- Four-bit address lookup and arithmetic are physically valid independently
of accumulator values or the arithmetic success predicate. -/
theorem montLookup_physical (L : MontStageLayout) (addr : List Wire) (K : Nat)
    (hn : (L.cin :: addr ++ L.table ++ L.acc ++ L.carry ++ L.scratch).Nodup)
    (ha : addr ≠ []) :
    GatePhysical (montLookupAdd L addr K) ∧ GatePhysical (montLookupSub L addr K) := by
  cases addr with
  | nil => exact False.elim (ha rfl)
  | cons a bs =>
    have ndlookup : (a :: bs ++ L.scratch ++ L.table).Nodup := by
      apply List.nodup_iff_count.mpr; intro q
      have h := List.nodup_iff_count.mp hn q
      simp only [List.count_cons,List.count_append] at h ⊢; omega
    have ndadd : (L.cin :: L.table ++ L.acc ++ L.carry).Nodup := by
      apply List.nodup_iff_count.mpr; intro q
      have h := List.nodup_iff_count.mp hn q
      simp only [List.count_cons,List.count_append] at h ⊢; omega
    have lk : GatePhysical (montLookup L (a::bs) K) :=
      lookup_physical a bs L.scratch L.table (fun d => d*K) ndlookup
    simp only [montLookupAdd,montLookupSub,gatePhysical_append]
    exact ⟨⟨⟨lk,addInPlace_physical _ _ _ _ ndadd⟩,lk⟩,
      ⟨⟨lk,subInPlace_physical _ _ _ _ ndadd⟩,lk⟩⟩

theorem montReduce_physical (L : MontStageLayout) (p i : Nat)
    (hn : (L.cin :: L.record i ++ L.table ++ L.acc ++ L.carry ++ L.scratch).Nodup)
    (hr : L.record i ≠ []) :
    GatePhysical (montReduce L p i) ∧ GatePhysical (montRestoreReduce L p i) := by
  have acc : L.acc.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h; omega
  have ndcopy : (L.acc.take 4 ++ L.record i).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist 4 L.acc).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have cp := copyRegister_physical none _ _ ndcopy (by simp)
  have lk := montLookup_physical L (L.record i) p hn hr
  have rot := rotateBits_physical L.acc 4 acc
  simp only [montReduce,montRestoreReduce,gatePhysical_append]
  exact ⟨⟨⟨cp,lk.1⟩,rot.1⟩,⟨⟨rot.2,lk.2⟩,cp⟩⟩

theorem montWindow_physical (L : MontStageLayout) (x y : List Wire) (p i : Nat)
    (hw : L.Widths) (hn : (x++y++L.wires).Nodup)
    (hi : i < 64) (hy : 256 ≤ y.length) :
    GatePhysical (montWindow L x y p i) ∧ GatePhysical (montRestoreWindow L x y p i) := by
  have hr : L.record i ≠ [] := by
    intro e
    have h := L.record_length hw i hi
    simp [e] at h
  have digit := montDigit_physical L x y i hn (by omega)
  have red := montReduce_physical L p i (L.reduce_nodup x y i hn) hr
  simp only [montWindow,montRestoreWindow,gatePhysical_append]
  exact ⟨⟨digit.1,red.1⟩,⟨red.2,digit.2⟩⟩

theorem constMontWindow_physical (L : MontStageLayout) (y : List Wire) (p K i : Nat)
    (hw : L.Widths) (hn : (y++L.wires).Nodup)
    (hi : i < 64) (hy : 256 ≤ y.length) :
    GatePhysical (constMontWindow L y p K i) ∧ GatePhysical (constMontRestoreWindow L y p K i) := by
  have hr : L.record i ≠ [] := by
    intro e; have h := L.record_length hw i hi; simp [e] at h
  have red := montReduce_physical L p i (L.reduce_nodup [] y i hn) hr
  have nd : (L.cin :: (y.drop (4*i)).take 4 ++ L.table ++ L.acc ++ L.carry ++ L.scratch).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := ((List.take_sublist 4 (y.drop (4*i))).trans (List.drop_sublist (4*i) y)).count_le q
    simp only [MontStageLayout.wires,MontStageLayout.work,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ha : (y.drop (4*i)).take 4 ≠ [] := by
    intro e
    have h := congrArg List.length e
    simp only [List.length_take,List.length_drop,List.length_nil] at h
    omega
  have lk := montLookup_physical L ((y.drop (4*i)).take 4) K nd ha
  simp only [constMontWindow,constMontRestoreWindow,gatePhysical_append]
  exact ⟨⟨lk.1,red.1⟩,⟨red.2,lk.2⟩⟩

end ECDSAAdd.Arithmetic
