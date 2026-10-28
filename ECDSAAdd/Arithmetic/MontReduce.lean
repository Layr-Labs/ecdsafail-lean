import ECDSAAdd.Arithmetic.MontNormalize

namespace ECDSAAdd.Arithmetic

/-- 固定寄存器低位的数值，不依赖重命名或额外复制。 -/
theorem mont_low_value (r : List Wire) (n : Nat) (hn : n≤r.length) (s : BasisState) :
    regValue (r.take n) s=regValue r s%2^n := by
  have hh := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at hh
  rw [hh,Nat.add_mul_mod_self_left]
  apply (Nat.mod_eq_of_lt ?_).symm
  simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s

/-- 单次约减记录低四位，查表加修正项，并实际右旋四位。 -/
theorem montReduce_correct (L : MontStageLayout) (p i U : Nat)
    (hnd : (L.cin::(L.record i++L.table++L.acc++L.carry++L.scratch)).Nodup)
    (hr : (L.record i).length=4) (hs : L.scratch.length=3)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hw : L.acc.length=261) (hp : p%16=15)
    (hK : ∀ d<16, d*p<2^L.table.length) (hfit : U+(U%16)*p<2^261)
    (s : State) (m : List Bool) (ha : regValue L.acc s.basis=U)
    (hz : regValue L.table s.basis=0) (hsc : regValue L.scratch s.basis=0)
    (hca : regValue L.carry s.basis=0) (hci : s.basis L.cin=false)
    (hrec : regValue (L.record i) s.basis=0) :
    (run (montReduce L p i) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w∉L.record i → (run (montReduce L p i) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montReduce L p i) m s).basis=(U+(U%16)*p)/16 ∧
    regValue (L.record i) (run (montReduce L p i) m s).basis=U%16 := by
  have hn := List.nodup_iff_count.mp hnd
  have accN : L.acc.Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have h := hn w
    simp only [List.count_cons,List.count_append] at h; omega
  have arN : (L.acc++L.record i).Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have h := hn w
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have hncopy : (L.acc.take 4++L.record i).Nodup :=
    ((List.take_sublist 4 L.acc).append_right _).nodup arN
  have accR : L.acc.Disjoint (L.record i) := (List.nodup_append'.mp arN).2.2
  have outsideR (r : List Wire) (hr' : r=L.table ∨ r=L.carry ∨ r=L.scratch) :
      r.Disjoint (L.record i) := by
    apply List.disjoint_left.mpr; intro w hw' hh
    have h := hn w; have h1 := List.count_pos_iff.mpr hw'; have h2 := List.count_pos_iff.mpr hh
    rcases hr' with rfl|rfl|rfl <;> simp only [List.count_cons,List.count_append] at h <;> omega
  have cinR : L.cin∉L.record i := by
    intro hh; have h := hn L.cin; have h1 := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  let cp := copyRegister none (L.acc.take 4) (L.record i)
  let s1 := run cp m s
  let m1 := m.drop (measurementCount cp)
  let s2 := run (montLookupAdd L (L.record i) p) m1 s1
  let m2 := m1.drop (measurementCount (montLookupAdd L (L.record i) p))
  have h1 := copyRegister_correct none (L.acc.take 4) (L.record i)
    (by simp [List.length_take,hw,hr]) hncopy (by simp) s m
  have keep1 (r : List Wire) (hr' : r.Disjoint (L.record i)) : regValue r s1.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw' => h1.2.1 w (List.disjoint_left.mp hr' hw'))
  have rec1 : regValue (L.record i) s1.basis=U%16 := by
    simpa only [copyValue,hrec,Nat.zero_xor,mont_low_value L.acc 4 (by omega),ha] using h1.2.2
  have h2 := montLookupAdd_correct L (L.record i) p hnd hr hs ht hc hK s1 m1
    ((keep1 _ (outsideR _ (Or.inl rfl))).trans hz)
    ((keep1 _ (outsideR _ (Or.inr (Or.inr rfl)))).trans hsc)
    ((keep1 _ (outsideR _ (Or.inr (Or.inl rfl)))).trans hca)
    ((h1.2.1 _ cinR).trans hci)
  have acc2 : regValue L.acc s2.basis=U+(U%16)*p := by
    rw [h2.2.2,keep1 L.acc accR,ha,rec1,hw,Nat.mod_eq_of_lt hfit]
  have hdiv : (U+(U%16)*p)%2^4=0 := by rw [montgomery_divisible p U hp]; simp
  have h3 := rotateRightBits_spec L.acc 4 (U+(U%16)*p) accN hdiv s2 m2 acc2
  have h3f := rotateBits_frame L.acc 4 s2 m2
  have hp' : montReduce L p i=cp++(montLookupAdd L (L.record i) p++rotateRightBits L.acc 4) := by
    simp only [montReduce,cp,List.append_assoc]
  rw [hp',run_append,run_take,run_append,run_take]
  change (run (rotateRightBits L.acc 4) m2 s2).phase=s.phase ∧ _
  refine ⟨h3.1.trans (h2.1.trans h1.1),?_,h3.2,?_⟩
  · intro w ha' hr'; exact (h3f.2.1 w ha').trans ((h2.2.1 w ha').trans (h1.2.1 w hr'))
  · have eq2 : regValue (L.record i) s2.basis=U%16 :=
      (regValue_congr _ _ _ (fun w hw' => h2.2.1 w (List.disjoint_left.mp accR.symm hw'))).trans rec1
    exact (regValue_congr _ _ _ (fun w hw' => h3f.2.1 w (List.disjoint_left.mp accR.symm hw'))).trans eq2


/-- 逆序约减以保存的低四位为契约，恢复 U 后清记录。 -/
theorem montRestoreReduce_correct (L : MontStageLayout) (p i U : Nat)
    (hnd : (L.cin::(L.record i++L.table++L.acc++L.carry++L.scratch)).Nodup)
    (hr : (L.record i).length=4) (hs : L.scratch.length=3)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hw : L.acc.length=261) (hp : p%16=15)
    (hK : ∀ d<16, d*p<2^L.table.length) (hfit : U+(U%16)*p<2^261)
    (s : State) (m : List Bool) (ha : regValue L.acc s.basis=(U+(U%16)*p)/16)
    (hz : regValue L.table s.basis=0) (hsc : regValue L.scratch s.basis=0)
    (hca : regValue L.carry s.basis=0) (hci : s.basis L.cin=false)
    (hrec : regValue (L.record i) s.basis=U%16) :
    (run (montRestoreReduce L p i) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w∉L.record i → (run (montRestoreReduce L p i) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montRestoreReduce L p i) m s).basis=U ∧
    regValue (L.record i) (run (montRestoreReduce L p i) m s).basis=0 := by
  have hn := List.nodup_iff_count.mp hnd
  have accN : L.acc.Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have h := hn w
    simp only [List.count_cons,List.count_append] at h; omega
  have arN : (L.acc++L.record i).Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have h := hn w
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have hncopy : (L.acc.take 4++L.record i).Nodup :=
    ((List.take_sublist 4 L.acc).append_right _).nodup arN
  have accR : L.acc.Disjoint (L.record i) := (List.nodup_append'.mp arN).2.2
  have outsideA (r : List Wire) (hr' : r=L.table ∨ r=L.carry ∨ r=L.scratch ∨ r=L.record i) :
      r.Disjoint L.acc := by
    apply List.disjoint_left.mpr; intro w hw' hh
    have h := hn w; have h1 := List.count_pos_iff.mpr hw'; have h2 := List.count_pos_iff.mpr hh
    rcases hr' with rfl|rfl|rfl|rfl <;> simp only [List.count_cons,List.count_append] at h <;> omega
  have cinA : L.cin∉L.acc := by
    intro hh; have h := hn L.cin; have h1 := List.count_pos_iff.mpr hh
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
  have exactDiv : 16*((U+(U%16)*p)/16)=U+(U%16)*p := by
    rw [montgomery_divisible p U hp]; simp
  have hrot : 2^4*((U+(U%16)*p)/16)<2^L.acc.length := by simpa only [hw,show 2^4=16 from rfl,exactDiv] using hfit
  let s1 := run (rotateLeftBits L.acc 4) m s
  let m1 := m.drop (measurementCount (rotateLeftBits L.acc 4))
  let s2 := run (montLookupSub L (L.record i) p) m1 s1
  let m2 := m1.drop (measurementCount (montLookupSub L (L.record i) p))
  have h1 := rotateLeftBits_spec L.acc 4 ((U+(U%16)*p)/16) accN hrot s m ha
  have h1f := rotateBits_frame L.acc 4 s m
  have keep1 (r : List Wire) (hr' : r.Disjoint L.acc) : regValue r s1.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw' => h1f.2.2.2 w (List.disjoint_left.mp hr' hw'))
  have rec1 : regValue (L.record i) s1.basis=U%16 :=
    (keep1 _ accR.symm).trans hrec
  have acc1 : regValue L.acc s1.basis=U+(U%16)*p := by simpa only [Holds.holds,show 2^4=16 from rfl,exactDiv] using h1.2
  have h2 := montLookupSub_correct L (L.record i) p hnd hr hs ht hc hK s1 m1
    ((keep1 _ (outsideA _ (Or.inl rfl))).trans hz)
    ((keep1 _ (outsideA _ (Or.inr (Or.inr (Or.inl rfl))))).trans hsc)
    ((keep1 _ (outsideA _ (Or.inr (Or.inl rfl)))).trans hca)
    ((h1f.2.2.2 _ cinA).trans hci)
  have acc2 : regValue L.acc s2.basis=U := by
    rw [h2.2.2,acc1,rec1,hw,show U+(U%16)*p+2^261-(U%16)*p=U+2^261 by omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  have rec2 : regValue (L.record i) s2.basis=U%16 :=
    (regValue_congr _ _ _ (fun w hw' => h2.2.1 w (List.disjoint_left.mp accR.symm hw'))).trans rec1
  have h3 := copyRegister_correct none (L.acc.take 4) (L.record i)
    (by simp [List.length_take,hw,hr]) hncopy (by simp) s2 m2
  have hp' : montRestoreReduce L p i=rotateLeftBits L.acc 4++
      (montLookupSub L (L.record i) p++copyRegister none (L.acc.take 4) (L.record i)) := by
    simp only [montRestoreReduce,List.append_assoc]
  rw [hp',run_append,run_take,run_append,run_take]
  change (run (copyRegister none (L.acc.take 4) (L.record i)) m2 s2).phase=s.phase ∧ _
  refine ⟨h3.1.trans (h2.1.trans h1.1),?_,?_,?_⟩
  · intro w ha' hr'; exact (h3.2.1 w hr').trans ((h2.2.1 w ha').trans (h1f.2.2.2 w ha'))
  · exact (regValue_congr _ _ _ (fun w hw' => h3.2.1 w (List.disjoint_left.mp accR hw'))).trans acc2
  · simpa only [copyValue,rec2,mont_low_value L.acc 4 (by omega),acc2,show 2^4=16 from rfl,Nat.xor_self] using h3.2.2

end ECDSAAdd.Arithmetic
