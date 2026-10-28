import ECDSAAdd.Arithmetic.MontLayout

namespace ECDSAAdd.Arithmetic

/-- P 在一份共享工作区上依次准备变量段和常数转换段，保存两套历史。 -/
theorem montP_correct (M : MontLayout) (p X Y : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (s : State) (m : List Bool)
    (vx : regValue M.x s.basis=X) (vy : regValue M.y s.basis=Y) (vw : regValue M.work s.basis=0) :
    (run (montP M p) m s).phase=s.phase ∧
    (∀ w, w∉M.work → (run (montP M p) m s).basis w=s.basis w) ∧
    MontPrepared M p X Y (run (montP M p) m s).basis := by
  have hpos : 0<p := Nat.Prime.pos Fact.out
  have clean (r : List Wire) (hr : r⊆M.work) := M.work_clean _ vw r hr
  have va : regValue M.a s.basis=0 := clean _ (by intro w h; simp [MontLayout.work,MontLayout.activeA,h])
  have vh : regValue M.hA s.basis=0 := clean _ (by intro w h; simp [MontLayout.work,MontLayout.activeA,h])
  have vf : s.basis M.fA=false := (regValue_zero _ _).mp vw _ (by simp [MontLayout.work,MontLayout.activeA])
  have vs : regValue M.shared s.basis=0 := clean _ (by intro w h; simp [MontLayout.work,h])
  have h1 := montPrepare_correct M.first M.x M.y p X Y hw.first (M.first_nodup hnd)
    (by rw [hw.x]; omega) (by rw [hw.y]) hp hp16 hX s m vx vy va vh vf vs
  generalize hs1 : run (montPrepare M.first M.x M.y p) m s=s1 at h1
  let m1 := m.drop (measurementCount (montPrepare M.first M.x M.y p))
  have keep1 (w : Wire) (hm : w∈M.x++M.y++M.out++M.activeZ++M.shared) : s1.basis w=s.basis w := by
    have hh := List.disjoint_left.mp (M.first_disjoint hnd) hm
    apply h1.2.1 w
    · exact fun h => hh (by simp [MontLayout.activeA,MontLayout.a,h])
    · exact fun h => hh (by simp [MontLayout.activeA,MontLayout.hA,h])
    · exact fun he => hh (by simp [MontLayout.activeA,MontLayout.fA,he])
  have keepReg1 (r : List Wire) (hr : r⊆M.x++M.y++M.out++M.activeZ++M.shared) : regValue r s1.basis=regValue r s.basis :=
    regValue_congr r s1.basis s.basis (fun w h => keep1 w (hr h))
  have vz : regValue M.z s1.basis=0 := (keepReg1 _ (by intro w h; simp [MontLayout.activeZ,h])).trans
    (clean _ (by intro w h; simp [MontLayout.work,MontLayout.activeZ,h]))
  have vhz : regValue M.hZ s1.basis=0 := (keepReg1 _ (by intro w h; simp [MontLayout.activeZ,h])).trans
    (clean _ (by intro w h; simp [MontLayout.work,MontLayout.activeZ,h]))
  have vfz : s1.basis M.fZ=false := (keep1 _ (by simp [MontLayout.activeZ])).trans
    ((regValue_zero _ _).mp vw _ (by simp [MontLayout.work,MontLayout.activeZ]))
  have vs1 : regValue M.shared s1.basis=0 := (keepReg1 _ (by intro w h; simp [h])).trans vs
  have hK := montgomeryConversion_bound p hpos
  have h2 := constPrepare_correct M.second M.a p (montgomeryConversion p) (montgomeryValue p X Y 64%p)
    (M.second_widths hw) (M.second_nodup hnd) (by change 256≤M.first.acc.length; rw [hw.first.acc]; omega)
    hp hp16 hK s1 m1 h1.2.2.1 vz vhz vfz vs1
  generalize ht : run (constPrepare M.second M.a p (montgomeryConversion p)) m1 s1=t at h2
  have keep2 (w : Wire) (hm : w∈M.x++M.y++M.out++M.activeA++M.shared) : t.basis w=s1.basis w := by
    have hh := List.disjoint_left.mp (M.second_disjoint hnd) hm
    apply h2.2.1 w
    · exact fun h => hh (by simp [MontLayout.activeZ,MontLayout.second] at h ⊢; exact Or.inl h)
    · exact fun h => hh (by simp only [MontLayout.second] at h; simp [MontLayout.activeZ,h])
    · exact fun he => hh (by simp only [MontLayout.second] at he; simp [MontLayout.activeZ,he])
  have keepReg2 (r : List Wire) (hr : r⊆M.x++M.y++M.out++M.activeA++M.shared) : regValue r t.basis=regValue r s1.basis :=
    regValue_congr r t.basis s1.basis (fun w h => keep2 w (hr h))
  have hconv := montgomery_two_stages p X Y hp16 (by rwa [montgomeryRadix_eq]) (by rwa [montgomeryRadix_eq])
  have hrun : run (montP M p) m s=t := by
    rw [montP,run_append,run_take,hs1]
    exact ht
  rw [hrun]
  refine ⟨h2.1.trans h1.1,?_,?_⟩
  · intro w hw'
    have ha : w∉M.activeA := fun h => hw' (by simp [MontLayout.work,h])
    have hz : w∉M.activeZ := fun h => hw' (by simp [MontLayout.work,h])
    exact (h2.2.1 w (fun h => hz (by simp [MontLayout.activeZ,MontLayout.second] at h ⊢; exact Or.inl h))
      (fun h => hz (by simp only [MontLayout.second] at h; simp [MontLayout.activeZ,h]))
      (fun he => hz (by simp only [MontLayout.second] at he; simp [MontLayout.activeZ,he]))).trans
      (h1.2.1 w (fun h => ha (by simp [MontLayout.activeA,MontLayout.a,h]))
        (fun h => ha (by simp [MontLayout.activeA,MontLayout.hA,h]))
        (fun he => ha (by simp [MontLayout.activeA,MontLayout.fA,he])))
  · refine ⟨?_,?_,?_,?_,?_,h2.2.2.2.1,?_,h2.2.2.2.2,?_⟩
    · exact (keepReg2 M.x (by intro w h; simp [h])).trans ((keepReg1 M.x (by intro w h; simp [h])).trans vx)
    · exact (keepReg2 M.y (by intro w h; simp [h])).trans ((keepReg1 M.y (by intro w h; simp [h])).trans vy)
    · exact (keepReg2 M.a (by intro w h; simp [MontLayout.activeA,h])).trans h1.2.2.1
    · exact h2.2.2.1.trans hconv
    · exact (keepReg2 M.hA (by intro w h; simp [MontLayout.activeA,h])).trans h1.2.2.2.1
    · exact (keep2 M.fA (by simp [MontLayout.activeA])).trans h1.2.2.2.2
    · exact (keepReg2 M.shared (by intro w h; simp [h])).trans vs1


/-- Q 按相反段序执行新的前向门列，消费两条历史并清空整个分配工作区。 -/
theorem montQ_correct (M : MontLayout) (p X Y : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15)
    (hX : X<p) (hY : Y<2^256) (s : State) (m : List Bool) (h : MontPrepared M p X Y s.basis) :
    (run (montQ M p) m s).phase=s.phase ∧
    (∀ w, w∉M.work → (run (montQ M p) m s).basis w=s.basis w) ∧
    regValue M.x (run (montQ M p) m s).basis=X ∧
    regValue M.y (run (montQ M p) m s).basis=Y ∧
    regValue M.work (run (montQ M p) m s).basis=0 := by
  have hpos : 0<p := Nat.Prime.pos Fact.out
  have hK := montgomeryConversion_bound p hpos
  have hconv := montgomery_two_stages p X Y hp16 (by rwa [montgomeryRadix_eq]) (by rwa [montgomeryRadix_eq])
  have h1 := constRestore_correct M.second M.a p (montgomeryConversion p) (montgomeryValue p X Y 64%p)
    (M.second_widths hw) (M.second_nodup hnd) (by change 256≤M.first.acc.length; rw [hw.first.acc]; omega)
    hp hp16 hK s m h.a (h.z.trans hconv.symm) h.hZ h.fZ h.shared
  generalize hs1 : run (constRestore M.second M.a p (montgomeryConversion p)) m s=s1 at h1
  let m1 := m.drop (measurementCount (constRestore M.second M.a p (montgomeryConversion p)))
  have keep1 (w : Wire) (hm : w∈M.x++M.y++M.out++M.activeA++M.shared) : s1.basis w=s.basis w := by
    have hh := List.disjoint_left.mp (M.second_disjoint hnd) hm
    apply h1.2.1 w
    · exact fun h => hh (by simp [MontLayout.activeZ,MontLayout.second] at h ⊢; exact Or.inl h)
    · exact fun h => hh (by simp only [MontLayout.second] at h; simp [MontLayout.activeZ,h])
    · exact fun he => hh (by simp only [MontLayout.second] at he; simp [MontLayout.activeZ,he])
  have keepReg1 (r : List Wire) (hr : r⊆M.x++M.y++M.out++M.activeA++M.shared) : regValue r s1.basis=regValue r s.basis :=
    regValue_congr r s1.basis s.basis (fun w h => keep1 w (hr h))
  have h2 := montRestore_correct M.first M.x M.y p X Y hw.first (M.first_nodup hnd)
    (by rw [hw.x]; omega) (by rw [hw.y]) hp hp16 hX s1 m1
    ((keepReg1 M.x (by intro w h; simp [h])).trans h.x)
    ((keepReg1 M.y (by intro w h; simp [h])).trans h.y)
    ((keepReg1 M.a (by intro w h; simp [MontLayout.activeA,h])).trans h.a)
    ((keepReg1 M.hA (by intro w h; simp [MontLayout.activeA,h])).trans h.hA)
    ((keep1 M.fA (by simp [MontLayout.activeA])).trans h.fA)
    ((keepReg1 M.shared (by intro w h; simp [h])).trans h.shared)
  generalize ht : run (montRestore M.first M.x M.y p) m1 s1=t at h2
  have keep2 (w : Wire) (hm : w∈M.x++M.y++M.out++M.activeZ++M.shared) : t.basis w=s1.basis w := by
    have hh := List.disjoint_left.mp (M.first_disjoint hnd) hm
    apply h2.2.1 w
    · exact fun h => hh (by simp [MontLayout.activeA,MontLayout.a,h])
    · exact fun h => hh (by simp [MontLayout.activeA,MontLayout.hA,h])
    · exact fun he => hh (by simp [MontLayout.activeA,MontLayout.fA,he])
  have keepReg2 (r : List Wire) (hr : r⊆M.x++M.y++M.out++M.activeZ++M.shared) : regValue r t.basis=regValue r s1.basis :=
    regValue_congr r t.basis s1.basis (fun w h => keep2 w (hr h))
  have vz : regValue M.z t.basis=0 := (keepReg2 M.z (by intro w h; simp [MontLayout.activeZ,h])).trans h1.2.2.1
  have vhz : regValue M.hZ t.basis=0 := (keepReg2 M.hZ (by intro w h; simp [MontLayout.activeZ,h])).trans h1.2.2.2.1
  have vfz : t.basis M.fZ=false := (keep2 M.fZ (by simp [MontLayout.activeZ])).trans h1.2.2.2.2
  have vs : regValue M.shared t.basis=0 := (keepReg2 M.shared (by intro w h; simp [h])).trans
    ((keepReg1 M.shared (by intro w h; simp [h])).trans h.shared)
  have hrun : run (montQ M p) m s=t := by
    rw [montQ,run_append,run_take,hs1]
    exact ht
  rw [hrun]
  refine ⟨h2.1.trans h1.1,?_,?_,?_,?_⟩
  · intro w hw'
    have ha : w∉M.activeA := fun h => hw' (by simp [MontLayout.work,h])
    have hz : w∉M.activeZ := fun h => hw' (by simp [MontLayout.work,h])
    exact (h2.2.1 w (fun h => ha (by simp [MontLayout.activeA,MontLayout.a,h]))
      (fun h => ha (by simp [MontLayout.activeA,MontLayout.hA,h]))
      (fun he => ha (by simp [MontLayout.activeA,MontLayout.fA,he]))).trans
      (h1.2.1 w (fun h => hz (by simp [MontLayout.activeZ,MontLayout.second] at h ⊢; exact Or.inl h))
        (fun h => hz (by simp only [MontLayout.second] at h; simp [MontLayout.activeZ,h]))
        (fun he => hz (by simp only [MontLayout.second] at he; simp [MontLayout.activeZ,he])))
  · exact (keepReg2 M.x (by intro w h; simp [h])).trans ((keepReg1 M.x (by intro w h; simp [h])).trans h.x)
  · exact (keepReg2 M.y (by intro w h; simp [h])).trans ((keepReg1 M.y (by intro w h; simp [h])).trans h.y)
  · apply (regValue_zero _ _).mpr
    intro w hw'
    simp only [MontLayout.work,MontLayout.activeA,MontLayout.activeZ,List.mem_append,List.mem_singleton] at hw'
    rcases hw' with (((ha|hha)|hfa)|((hz|hhz)|hfz))|hs
    · exact (regValue_zero _ _).mp h2.2.2.1 w ha
    · exact (regValue_zero _ _).mp h2.2.2.2.1 w hha
    · simpa only [hfa] using h2.2.2.2.2
    · exact (regValue_zero _ _).mp vz w hz
    · exact (regValue_zero _ _).mp vhz w hhz
    · simpa only [hfz] using vfz
    · exact (regValue_zero _ _).mp vs w hs

/-- P 的内部 Triple：输入为规范 X 和任意256位 Y，所有工作位从零开始。 -/
theorem montP_spec (M : MontLayout) (p X Y : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15) (hX : X<p) (hY : Y<2^256) :
    Triple (fun s => regValue M.x s=X ∧ regValue M.y s=Y ∧ regValue M.work s=0)
      (montP M p) (MontPrepared M p X Y) := by
  intro s m h
  have hh := montP_correct M p X Y hw hnd hp hp16 hX hY s m h.1 h.2.1 h.2.2
  exact ⟨hh.1,hh.2.2⟩

/-- Q 只消费准备契约，不要求输出寄存器为零，供五个适配器共同复用。 -/
theorem montQ_spec (M : MontLayout) (p X Y : Nat) [Fact p.Prime]
    (hw : M.Widths) (hnd : M.wires.Nodup) (hp : p<2^256) (hp16 : p%16=15) (hX : X<p) (hY : Y<2^256) :
    Triple (MontPrepared M p X Y) (montQ M p)
      (fun s => regValue M.x s=X ∧ regValue M.y s=Y ∧ regValue M.work s=0) := by
  intro s m h
  have hh := montQ_correct M p X Y hw hnd hp hp16 hX hY s m h
  exact ⟨hh.1,hh.2.2⟩

end ECDSAAdd.Arithmetic
