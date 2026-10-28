import ECDSAAdd.Arithmetic.ConstDigit

namespace ECDSAAdd.Arithmetic

/-- 常数窗口同时推进累加器和四位历史整数；不把非零历史当作已清工作区。 -/
theorem constMontWindow_correct (L : MontStageLayout) (y : List Wire) (p i X Y A H : Nat)
    (hw : L.Widths) (hnd : (y++L.wires).Nodup) (hy : 256≤y.length)
    (hi : i<64) (hp : p<2^256) (hp16 : p%16=15) (hX : X<p) (hA : A<2*p) (hH : H<16^i)
    (s : State) (m : List Bool) (vy : regValue y s.basis=Y)
    (va : regValue L.acc s.basis=A) (vh : regValue L.history s.basis=H) (vw : regValue L.work s.basis=0) :
    (run (constMontWindow L y p X i) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w∉L.history → (run (constMontWindow L y p X i) m s).basis w=s.basis w) ∧
    regValue L.acc (run (constMontWindow L y p X i) m s).basis=montgomeryStep p A X ((Y/16^i)%16) ∧
    regValue L.history (run (constMontWindow L y p X i) m s).basis=
      H+16^i*((A+((Y/16^i)%16)*X)%16) := by
  have hpow : 2^(4*i)=16^i := by rw [Nat.pow_mul]
  have hbound : 4*i+4≤L.history.length := by rw [hw.history]; omega
  have hd : (Y/16^i)%16<16 := Nat.mod_lt _ (by decide)
  have hfit : A+16*X<2^261 := by omega
  let D := (Y/16^i)%16
  let U := A+X*D
  have hu : U+(U%16)*p<2^261 := by
    have hh := montgomery_window_bound p A X D hA hX hd
    have he : U=A+D*X := by dsimp only [U]; rw [Nat.mul_comm X]
    rw [he]
    exact lt_of_lt_of_le hh (by omega)
  have hK : ∀ d<16, d*p<2^L.table.length := by
    intro d hd'
    have hh := Nat.mul_le_mul_right p (show d≤15 by omega)
    rw [hw.table]; omega
  have h1 := constDigitAdd_correct L y i X Y A hw hnd hy hi (by omega) hfit s m vy va vw
  let s1 := run (montLookupAdd L ((y.drop (4*i)).take 4) X) m s
  let m1 := m.drop (measurementCount (montLookupAdd L ((y.drop (4*i)).take 4) X))
  have ad := L.acc_disjoint [] y hnd
  have keep1 (r : List Wire) (hr : r⊆y++L.history++[L.flag]++L.work) : regValue r s1.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw' => h1.2.1 w (List.disjoint_left.mp ad (hr hw')))
  have hist1 : regValue L.history s1.basis=H := (keep1 _ (by intro w hh; simp [hh])).trans vh
  have work1 : regValue L.work s1.basis=0 := (keep1 _ (by intro w hh; simp [hh])).trans vw
  have rec1 : regValue (L.record i) s1.basis=0 := by
    rw [MontStageLayout.record,mont_low_value _ 4 (by simp only [List.length_drop]; omega),
      mont_drop_value L.history (4*i) (by omega),hist1,hpow,Nat.div_eq_of_lt hH]
    rfl
  have clean1 (r : List Wire) (hr : r⊆L.work) : regValue r s1.basis=0 := L.work_clean _ work1 r hr
  have h2 := montReduce_correct L p i U (L.reduce_nodup [] y i hnd) (L.record_length hw i hi) hw.scratch
    (hw.table.trans hw.acc.symm) (by rw [hw.carry,hw.acc]) hw.acc hp16 hK hu s1 m1 h1.2.2
    (clean1 L.table (by intro w hh; simp [MontStageLayout.work,hh])) (clean1 L.scratch (by intro w hh; simp [MontStageLayout.work,hh]))
    (clean1 L.carry (by intro w hh; simp [MontStageLayout.work,hh])) (L.cin_clean _ work1) rec1
  have hprog : constMontWindow L y p X i=montLookupAdd L ((y.drop (4*i)).take 4) X++montReduce L p i := rfl
  rw [hprog,run_append,run_take]
  let t := run (montReduce L p i) m1 s1
  have keep (w : Wire) (ha' : w∉L.acc) (hr : w∉L.record i) : t.basis w=s.basis w :=
    (h2.2.1 w ha' hr).trans (h1.2.1 w ha')
  refine ⟨h2.1.trans h1.1,?_,?_,?_⟩
  · intro w ha' hh; exact keep w ha' (fun hr => hh ((L.record_sublist i).subset hr))
  · simpa only [montgomeryStep,U,D,Nat.mul_comm X] using h2.2.2.1
  · have hh := mont_replace_value L.history (4*i) 4 hbound (L.history_nodup [] y hnd) s.basis t.basis
      (fun w hw' hr => keep w (List.disjoint_left.mp ad (by simp [hw'])) hr)
    have hle : 16^i≤2^(4*i+4) := by
      rw [Nat.pow_add,hpow]; omega
    have htail : H/2^(4*i+4)=0 := Nat.div_eq_of_lt (by omega)
    rw [vh,hpow,Nat.mod_eq_of_lt hH,htail,Nat.mul_zero,Nat.add_zero] at hh
    change regValue L.history t.basis=_
    rw [hh,show regValue ((L.history.drop (4*i)).take 4) t.basis=U%16 from h2.2.2.2]
    simp only [U,D,Nat.mul_comm X]


/-- 恢复窗口以累加器与整条历史的精确关系为前提。 -/
theorem constMontRestoreWindow_correct (L : MontStageLayout) (y : List Wire) (p i X Y A H : Nat)
    (hw : L.Widths) (hnd : (y++L.wires).Nodup) (hy : 256≤y.length)
    (hi : i<64) (hp : p<2^256) (hp16 : p%16=15) (hX : X<p) (hA : A<2*p) (hH : H<16^i)
    (s : State) (m : List Bool) (vy : regValue y s.basis=Y)
    (va : regValue L.acc s.basis=montgomeryStep p A X ((Y/16^i)%16)) (vh : regValue L.history s.basis=H+16^i*((A+((Y/16^i)%16)*X)%16)) (vw : regValue L.work s.basis=0) :
    (run (constMontRestoreWindow L y p X i) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w∉L.history → (run (constMontRestoreWindow L y p X i) m s).basis w=s.basis w) ∧
    regValue L.acc (run (constMontRestoreWindow L y p X i) m s).basis=A ∧
    regValue L.history (run (constMontRestoreWindow L y p X i) m s).basis=H := by
  have hpow : 2^(4*i)=16^i := by rw [Nat.pow_mul]
  have hbound : 4*i+4≤L.history.length := by rw [hw.history]; omega
  have hd : (Y/16^i)%16<16 := Nat.mod_lt _ (by decide)
  have hfit : A+16*X<2^261 := by omega
  let D := (Y/16^i)%16
  let U := A+X*D
  have hu : U+(U%16)*p<2^261 := by
    have hh := montgomery_window_bound p A X D hA hX hd
    have he : U=A+D*X := by dsimp only [U]; rw [Nat.mul_comm X]
    rw [he]
    exact lt_of_lt_of_le hh (by omega)
  have hK : ∀ d<16, d*p<2^L.table.length := by
    intro d hd'
    have hh := Nat.mul_le_mul_right p (show d≤15 by omega)
    rw [hw.table]; omega
  have vhU : regValue L.history s.basis=H+16^i*(U%16) := by
    simpa only [U,D,Nat.mul_comm X] using vh
  have hM : U%16<16 := Nat.mod_lt _ (by decide)
  have htop : H+16^i*(U%16)<2^(4*i+4) := by
    have hh := Nat.mul_le_mul_left (16^i) (show U%16≤15 by omega)
    rw [Nat.pow_add,hpow]; change H+16^i*(U%16)<16^i*16; omega
  have hrecord : regValue (L.record i) s.basis=U%16 := by
    rw [MontStageLayout.record,mont_low_value _ 4 (by simp only [List.length_drop]; omega),
      mont_drop_value L.history (4*i) (by omega),vhU,hpow,
      Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt hH,Nat.zero_add]
    exact Nat.mod_eq_of_lt hM
  have clean (r : List Wire) (hr : r⊆L.work) : regValue r s.basis=0 := L.work_clean _ vw r hr
  have haU : regValue L.acc s.basis=(U+(U%16)*p)/16 := by
    simpa only [montgomeryStep,U,D,Nat.mul_comm X] using va
  have h1 := montRestoreReduce_correct L p i U (L.reduce_nodup [] y i hnd) (L.record_length hw i hi) hw.scratch
    (hw.table.trans hw.acc.symm) (by rw [hw.carry,hw.acc]) hw.acc hp16 hK hu s m haU
    (clean L.table (by intro w hh; simp [MontStageLayout.work,hh]))
    (clean L.scratch (by intro w hh; simp [MontStageLayout.work,hh]))
    (clean L.carry (by intro w hh; simp [MontStageLayout.work,hh])) (L.cin_clean _ vw) hrecord
  let s1 := run (montRestoreReduce L p i) m s
  let m1 := m.drop (measurementCount (montRestoreReduce L p i))
  have ad := L.inputs_disjoint [] y hnd
  have keep1 (r : List Wire) (hr : r⊆y++[L.flag]++L.work) : regValue r s1.basis=regValue r s.basis := by
    apply regValue_congr; intro w hw'
    have hh := List.disjoint_left.mp ad (hr hw')
    exact h1.2.1 w (fun hm => hh (List.mem_append_left _ hm))
      (fun hm => hh (List.mem_append_right _ ((L.record_sublist i).subset hm)))
  have work1 : regValue L.work s1.basis=0 := (keep1 _ (by intro w hh; simp [hh])).trans vw
  have h2 := constDigitSub_correct L y i X Y A hw hnd hy hi (by omega) hfit s1 m1
    ((keep1 y (by intro w hh; simp [hh])).trans vy) h1.2.2.1 work1
  rw [constMontRestoreWindow,run_append,run_take]
  let t := run (montLookupSub L ((y.drop (4*i)).take 4) X) m1 s1
  have keep (w : Wire) (ha' : w∉L.acc) (hr : w∉L.record i) : t.basis w=s.basis w :=
    (h2.2.1 w ha').trans (h1.2.1 w ha' hr)
  refine ⟨h2.1.trans h1.1,?_,h2.2.2,?_⟩
  · intro w ha' hh; exact keep w ha' (fun hr => hh ((L.record_sublist i).subset hr))
  · have ad' := L.acc_disjoint [] y hnd
    have histA (w : Wire) (hh : w∈L.history) : w∉L.acc := List.disjoint_left.mp ad' (by simp [hh])
    have hrec : regValue (L.record i) t.basis=0 :=
      (regValue_congr _ _ _ (fun w hw' => h2.2.1 w (histA w ((L.record_sublist i).subset hw')))).trans h1.2.2.2
    have hh := mont_replace_value L.history (4*i) 4 hbound (L.history_nodup [] y hnd) s.basis t.basis
      (fun w hw' hr => keep w (histA w hw') hr)
    simp only [MontStageLayout.record] at hrec
    rw [vhU,hpow,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hH,
      Nat.div_eq_of_lt htop,hrec,Nat.mul_zero,Nat.add_zero,Nat.mul_zero,Nat.add_zero] at hh
    exact hh

end ECDSAAdd.Arithmetic
