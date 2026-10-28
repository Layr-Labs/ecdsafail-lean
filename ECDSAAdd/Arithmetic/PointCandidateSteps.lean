import ECDSAAdd.Arithmetic.PointCandidateState

namespace ECDSAAdd.Arithmetic

private theorem pool_zero (L : PointAddLayout) (h : L.Widths) (st : BasisState)
    (hz : regValue L.pool st=0) (n : Nat) (hn : n≤5699) :
    regValue (wireBlock L.poolWire 0 n) st=0 := by
  rw [L.pool_prefix h n hn]
  apply (regValue_zero _ _).mpr
  intro w hw
  exact (regValue_zero _ _).mp hz w ((List.take_sublist n L.pool).subset hw)

theorem CandidateValues.sub (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (v : CandidateField → Nat) (G : Bool) (a b o : CandidateField)
    (ha : (L.reg a).length=257) (hb : (L.reg b).length=257) (ho : (L.reg o).length=257)
    (hn : (L.reg a++L.reg b++L.reg o++L.pool).Nodup) (hA : v a<p) (hB : v b<p) :
    Triple (CandidateValues L v G) (fieldSub (poolSub L.poolWire (L.reg a) (L.reg b) (L.reg o)))
      (CandidateValues L (Function.update v o (v o ^^^ ((v a+p-v b)%p))) G) := by
  intro s m hv
  have hi := poolSub_inputs L.poolWire (L.reg a) (L.reg b) (L.reg o) ha hb ho
  have hw : regValue (poolSub L.poolWire (L.reg a) (L.reg b) (L.reg o)).work s.basis=0 := by
    rw [poolSub_work]
    exact pool_zero L h s.basis hv.2.1 1287 (by omega)
  obtain ⟨hp,he,hr⟩ := fieldSub_correct _ (L.poolSub_nodup h _ _ _ ha hb ho hn) (poolSub_width _ _ _ _) s m
    (by rw [hi.1,hv.1 a]; exact hA) (by rw [hi.2.1,hv.1 b]; exact hB) hw
  generalize hrun : run (fieldSub (poolSub L.poolWire (L.reg a) (L.reg b) (L.reg o))) m s=t at hp he hr ⊢
  rw [hi.2.2] at he hr
  refine ⟨hp,CandidateValues.update L hnd v G o _ s.basis t.basis hv he ?_⟩
  simpa only [hi.1,hi.2.1,hv.1 a,hv.1 b,hv.1 o] using hr

theorem CandidateValues.constant (L : PointAddLayout) (hnd : L.wires.Nodup)
    (v : CandidateField → Nat) (G : Bool) (o : CandidateField) (k : Nat)
    (hk : k<2^(L.reg o).length) :
    Triple (CandidateValues L v G) (xorConstant (L.reg o) k)
      (CandidateValues L (Function.update v o (v o ^^^ k)) G) := by
  intro s m hv
  have hn := (List.nodup_append'.mp (L.reg_pool_nodup hnd o)).1
  obtain ⟨hp,he,hr⟩ := xorConstant_correct (L.reg o) hn k hk s m
  exact ⟨hp,CandidateValues.update L hnd v G o _ s.basis _ hv he (by simpa only [hv.1 o] using hr)⟩

theorem CandidateValues.copy (L : PointAddLayout) (hnd : L.wires.Nodup)
    (v : CandidateField → Nat) (G : Bool) (a o : CandidateField) (hao : a≠o)
    (hlen : (L.reg a).length=(L.reg o).length) :
    Triple (CandidateValues L v G) (copyRegister none (L.reg a) (L.reg o))
      (CandidateValues L (Function.update v o (v o ^^^ v a)) G) := by
  intro s m hv
  have hn : (L.reg a++L.reg o).Nodup := List.nodup_append'.mpr
    ⟨(List.nodup_append'.mp (L.reg_pool_nodup hnd a)).1,
     (List.nodup_append'.mp (L.reg_pool_nodup hnd o)).1,L.reg_disjoint hnd a o hao⟩
  obtain ⟨hp,he,hr⟩ := copyRegister_correct none (L.reg a) (L.reg o) hlen hn (by simp) s m
  exact ⟨hp,CandidateValues.update L hnd v G o _ s.basis _ hv he (by simpa only [copyValue,hv.1 a,hv.1 o] using hr)⟩

theorem CandidateValues.inverse (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (v : CandidateField → Nat) (G : Bool) (a o : CandidateField)
    (ha : (L.reg a).length=256) (ho : (L.reg o).length=256)
    (hn : (L.reg a++L.reg o++L.pool).Nodup) (hA0 : 0<v a) (hA : v a<p) :
    Triple (CandidateValues L v G) (fieldInverse (poolInverse L.poolWire (L.reg a) (L.reg o)))
      (CandidateValues L (Function.update v o (v o ^^^ ((v a : Fp)⁻¹).val)) G) := by
  intro s m hv
  have hi := poolInverse_inputs L.poolWire (L.reg a) (L.reg o) ho
  have hw : regValue (poolInverse L.poolWire (L.reg a) (L.reg o)).work s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro w hw
    exact (regValue_zero _ _).mp (pool_zero L h s.basis hv.2.1 5699 (by omega)) w
      ((poolInverse_work_perm _ _ _ ho).mem_iff.mp hw)
  obtain ⟨hp,he,hr⟩ := fieldInverse_correct _ (L.poolInverse_nodup h _ _ ho hn)
    (poolInverse_widths _ _ _ ha ho) s m
    (by rw [hi.1,hv.1 a]; exact hA0) (by rw [hi.1,hv.1 a]; exact hA) hw
  generalize hrun : run (fieldInverse (poolInverse L.poolWire (L.reg a) (L.reg o))) m s=t at hp he hr ⊢
  rw [hi.2] at he hr
  refine ⟨hp,CandidateValues.update L hnd v G o _ s.basis t.basis hv he ?_⟩
  simpa only [hi.1,hv.1 a,hv.1 o] using hr

theorem CandidateValues.mul (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (v : CandidateField → Nat) (G : Bool) (a b o : CandidateField)
    (ha : (L.reg a).length=257) (hb : 256≤(L.reg b).length) (ho : (L.reg o).length=257)
    (hn : (L.reg a++(L.reg b).take 256++L.reg o++L.pool).Nodup)
    (hA : v a<p) (hB : v b<2^256) :
    Triple (CandidateValues L v G)
      (fieldMul (poolMul L.poolWire (L.reg a) ((L.reg b).take 256) (L.reg o)))
      (CandidateValues L (Function.update v o (v o ^^^ ((v a*v b)%p))) G) := by
  intro s m hv
  have hbl : ((L.reg b).take 256).length=256 := by simp [Nat.min_eq_left hb]
  have hi := poolMul_inputs L.poolWire (L.reg a) ((L.reg b).take 256) (L.reg o)
  have hvb : regValue ((L.reg b).take 256) s.basis=v b := by
    have hl := regValue_low_iff ((L.reg b).take 256) ((L.reg b).drop 256) s.basis (v b)
      (by rw [hbl]; exact hB)
    rw [List.take_append_drop] at hl
    exact (hl.mp (hv.1 b)).1
  have hw : regValue (poolMul L.poolWire (L.reg a) ((L.reg b).take 256) (L.reg o)).work s.basis=0 := by
    rw [poolMul_work]
    exact pool_zero L h s.basis hv.2.1 1827 (by omega)
  obtain ⟨hp,he,hr⟩ := fieldMul_correct _ (L.poolMul_nodup h _ _ _ hn)
    (poolMul_widths _ _ _ _ ha hbl ho)  s m
    (by rw [hi.1,hv.1 a]; exact hA) hw
  generalize hrun : run (fieldMul (poolMul L.poolWire (L.reg a) ((L.reg b).take 256) (L.reg o))) m s=t at hp he hr ⊢
  rw [hi.2.2] at he hr
  refine ⟨hp,CandidateValues.update L hnd v G o _ s.basis t.basis hv he ?_⟩
  simpa only [hi.1,hi.2.1,hv.1 a,hvb,hv.1 o] using hr

theorem CandidateValues.safe (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (v : CandidateField → Nat) (G : Bool) (hX : v .dx<2^256) :
    Triple (CandidateValues L v G)
      (safeDivisor L.generic (L.dx.take 256) L.divisor.head! L.divisor.tail)
      (CandidateValues L (Function.update v .divisor (v .divisor ^^^ (if G then v .dx else 1))) G) := by
  intro s m hv
  have hdx := h.words L.dx (by simp [PointAddLayout.words])
  have hd : L.divisor.head!::L.divisor.tail=L.divisor :=
    List.cons_head!_tail (by intro he; have hh := h.divisor; rw [he] at hh; simp at hh)
  have hn : (L.generic::L.dx.take 256++L.divisor).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hnd w
    have ht := (List.take_sublist 256 L.dx).count_le w
    simp only [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.words,
      PointAddLayout.flags,PointAddLayout.pointWires,List.flatten_cons,List.flatten_nil,
      List.append_nil,List.count_append,List.count_cons,List.count_nil] at hh ⊢
    omega
  have hvx : regValue (L.dx.take 256) s.basis=v .dx := by
    have hl := regValue_low_iff (L.dx.take 256) (L.dx.drop 256) s.basis (v .dx)
      (by simpa [hdx] using hX)
    rw [List.take_append_drop] at hl
    exact (hl.mp (hv.1 .dx)).1
  obtain ⟨hp,he,hr⟩ := safeDivisor_correct L.generic (L.dx.take 256) L.divisor.head! L.divisor.tail
    (by rw [hd]; simp [hdx,h.divisor]) (by rw [hd]; exact hn) s m
  generalize hrun : run (safeDivisor L.generic (L.dx.take 256) L.divisor.head! L.divisor.tail) m s=t at hp he hr ⊢
  rw [hd] at he hr
  refine ⟨hp,CandidateValues.update L hnd v G .divisor _ s.basis t.basis hv he ?_⟩
  simpa only [hv.2.2,hvx,show regValue L.divisor s.basis=v .divisor from hv.1 .divisor] using hr

end ECDSAAdd.Arithmetic
