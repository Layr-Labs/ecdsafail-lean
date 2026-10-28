import ECDSAAdd.Arithmetic.ConstRounds

namespace ECDSAAdd.Arithmetic

/-- 变量段公开准备契约：记录带与借位明确保留，临时工作区归零。 -/
private theorem montPreparePrefix_correct (L : MontStageLayout) (x y : List Wire) (p k X Y : Nat)
    (hw : L.Widths) (hnd : (x++y++L.wires).Nodup) (hx : 256≤x.length) (hy : 256≤y.length)
    (hk : k≤64) (hp : p<2^256) (hp16 : p%16=15) (hX : X<p)
    (s : State) (m : List Bool) (vx : regValue x s.basis=X) (vy : regValue y s.basis=Y)
    (va : regValue L.acc s.basis=0) (vh : regValue L.history s.basis=0)
    (vf : s.basis L.flag=false) (vw : regValue L.work s.basis=0) :
    (run ((montPrepareRounds L x y p k ++ montNormalize L p)) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w∉L.history → w≠L.flag → (run ((montPrepareRounds L x y p k ++ montNormalize L p)) m s).basis w=s.basis w) ∧
    regValue L.acc (run ((montPrepareRounds L x y p k ++ montNormalize L p)) m s).basis=montgomeryValue p X Y k%p ∧
    regValue L.history (run ((montPrepareRounds L x y p k ++ montNormalize L p)) m s).basis=montgomeryQuotient p X Y k ∧
    (run ((montPrepareRounds L x y p k ++ montNormalize L p)) m s).basis L.flag=decide (montgomeryValue p X Y k<p) := by
  have h1 := montPrepareRounds_correct L x y p k X Y hw hnd hx hy hk hp hp16 hX s m vx vy va vh vw
  let s1 := run (montPrepareRounds L x y p k) m s
  let m1 := m.drop (measurementCount (montPrepareRounds L x y p k))
  have ad := L.inputs_disjoint x y hnd
  have keep1 (w : Wire) (hw' : w∈x++y++[L.flag]++L.work) : s1.basis w=s.basis w := by
    have hh := List.disjoint_left.mp ad hw'
    exact h1.2.1 w (fun hm => hh (List.mem_append_left _ hm)) (fun hm => hh (List.mem_append_right _ hm))
  have work1 : regValue L.work s1.basis=0 :=
    (regValue_congr _ _ _ (fun w hw' => keep1 w (by simp [hw']))).trans vw
  have clean (r : List Wire) (hr : r⊆L.work) := L.work_clean _ work1 r hr
  have h2 := montNormalize_correct L p (montgomeryValue p X Y k) (L.normalize_nodup x y hnd)
    (hw.table.trans hw.acc.symm) (by rw [hw.carry,hw.acc]) hw.acc hp (montgomeryValue_bound p X Y k hX)
    s1 m1 h1.2.2.1 (clean L.table (by intro w hh; simp [MontStageLayout.work,hh]))
    (clean L.carry (by intro w hh; simp [MontStageLayout.work,hh])) (L.cin_clean _ work1)
    ((keep1 _ (by simp)).trans vf)
  rw [run_append,run_take]
  refine ⟨h2.1.trans h1.1,fun w ha hh hf => (h2.2.1 w ha hf).trans (h1.2.1 w ha hh),h2.2.2.1,?_,h2.2.2.2⟩
  have ha := L.acc_disjoint x y hnd
  apply Eq.trans (regValue_congr _ _ _ ?_) h1.2.2.2
  intro w hw'
  apply h2.2.1 w (List.disjoint_left.mp ha (by simp [hw']))
  intro he; subst w
  have hh := List.nodup_iff_count.mp hnd L.flag
  have hm := List.count_pos_iff.mpr hw'
  simp only [MontStageLayout.wires,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at hh; omega

private theorem montPreparePrefix_spec (L : MontStageLayout) (x y : List Wire) (p k X Y : Nat)
    (hw : L.Widths) (hnd : (x++y++L.wires).Nodup) (hx : 256≤x.length) (hy : 256≤y.length)
    (hk : k≤64) (hp : p<2^256) (hp16 : p%16=15) (hX : X<p) :
    {{ x=X,y=Y,L.acc=0,L.history=0,L.flag=false,L.work=0 }} (montPrepareRounds L x y p k ++ montNormalize L p)
    {{ x=X,y=Y,L.acc=montgomeryValue p X Y k%p,L.history=montgomeryQuotient p X Y k,
       L.flag=decide (montgomeryValue p X Y k<p),L.work=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  rcases h with ⟨⟨⟨⟨⟨vx,vy⟩,va⟩,vh⟩,vf⟩,vw⟩
  have hh := montPreparePrefix_correct L x y p k X Y hw hnd hx hy hk hp hp16 hX s m vx vy va vh vf vw
  have hd := L.stable_disjoint x y hnd
  have keep (r : List Wire) (hr : r⊆x++y++L.work) : regValue r (run ((montPrepareRounds L x y p k ++ montNormalize L p)) m s).basis=regValue r s.basis := by
    apply regValue_congr; intro w hw'
    have hn := List.disjoint_left.mp hd (hr hw')
    exact hh.2.1 w (fun hm => hn (by simp [hm])) (fun hm => hn (by simp [hm])) (fun he => hn (by simp [he]))
  exact ⟨hh.1,⟨⟨⟨⟨(keep x (by intro w hw'; simp [hw'])).trans vx,
    (keep y (by intro w hw'; simp [hw'])).trans vy⟩,hh.2.2.1⟩,hh.2.2.2.1⟩,hh.2.2.2.2⟩,
    (keep L.work (by intro w hw'; simp [hw'])).trans vw⟩

theorem montPrepare_correct (L : MontStageLayout) (x y : List Wire) (p X Y : Nat)
    (hw : L.Widths) (hnd : (x++y++L.wires).Nodup) (hx : 256≤x.length) (hy : 256≤y.length)
    (hp : p<2^256) (hp16 : p%16=15) (hX : X<p)
    (s : State) (m : List Bool) (vx : regValue x s.basis=X) (vy : regValue y s.basis=Y)
    (va : regValue L.acc s.basis=0) (vh : regValue L.history s.basis=0)
    (vf : s.basis L.flag=false) (vw : regValue L.work s.basis=0) :
    (run (montPrepare L x y p) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w∉L.history → w≠L.flag → (run (montPrepare L x y p) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montPrepare L x y p) m s).basis=montgomeryValue p X Y 64%p ∧
    regValue L.history (run (montPrepare L x y p) m s).basis=montgomeryQuotient p X Y 64 ∧
    (run (montPrepare L x y p) m s).basis L.flag=decide (montgomeryValue p X Y 64<p) := by
  simpa only [montPrepare] using montPreparePrefix_correct L x y p 64 X Y hw hnd hx hy (by omega) hp hp16 hX s m vx vy va vh vf vw

theorem montPrepare_spec (L : MontStageLayout) (x y : List Wire) (p X Y : Nat)
    (hw : L.Widths) (hnd : (x++y++L.wires).Nodup) (hx : 256≤x.length) (hy : 256≤y.length)
    (hp : p<2^256) (hp16 : p%16=15) (hX : X<p) :
    {{ x=X,y=Y,L.acc=0,L.history=0,L.flag=false,L.work=0 }} montPrepare L x y p
    {{ x=X,y=Y,L.acc=montgomeryValue p X Y 64%p,L.history=montgomeryQuotient p X Y 64,
       L.flag=decide (montgomeryValue p X Y 64<p),L.work=0 }} := by
  exact montPreparePrefix_spec L x y p 64 X Y hw hnd hx hy (by omega) hp hp16 hX


private theorem montRestorePrefix_correct (L : MontStageLayout) (x y : List Wire) (p k X Y : Nat)
    (hw : L.Widths) (hnd : (x++y++L.wires).Nodup) (hx : 256≤x.length) (hy : 256≤y.length)
    (hk : k≤64) (hp : p<2^256) (hp16 : p%16=15) (hX : X<p)
    (s : State) (m : List Bool) (vx : regValue x s.basis=X) (vy : regValue y s.basis=Y)
    (va : regValue L.acc s.basis=montgomeryValue p X Y k%p) (vh : regValue L.history s.basis=montgomeryQuotient p X Y k)
    (vf : s.basis L.flag=decide (montgomeryValue p X Y k<p)) (vw : regValue L.work s.basis=0) :
    (run ((montDenormalize L p ++ montRestoreRounds L x y p k)) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w∉L.history → w≠L.flag → (run ((montDenormalize L p ++ montRestoreRounds L x y p k)) m s).basis w=s.basis w) ∧
    regValue L.acc (run ((montDenormalize L p ++ montRestoreRounds L x y p k)) m s).basis=0 ∧
    regValue L.history (run ((montDenormalize L p ++ montRestoreRounds L x y p k)) m s).basis=0 ∧
    (run ((montDenormalize L p ++ montRestoreRounds L x y p k)) m s).basis L.flag=false := by
  have clean (r : List Wire) (hr : r⊆L.work) := L.work_clean _ vw r hr
  have h1 := montDenormalize_correct L p (montgomeryValue p X Y k) (L.normalize_nodup x y hnd)
    (hw.table.trans hw.acc.symm) (by rw [hw.carry,hw.acc]) hw.acc hp (montgomeryValue_bound p X Y k hX)
    s m va (clean L.table (by intro w hh; simp [MontStageLayout.work,hh]))
    (clean L.carry (by intro w hh; simp [MontStageLayout.work,hh])) (L.cin_clean _ vw) vf
  let s1 := run (montDenormalize L p) m s
  let m1 := m.drop (measurementCount (montDenormalize L p))
  have keep1 (w : Wire) (hw' : w∈x++y++L.history++L.work) : s1.basis w=s.basis w := by
    have hh := List.nodup_iff_count.mp hnd w
    have hm := List.count_pos_iff.mpr hw'
    simp only [MontStageLayout.wires,List.count_append,List.count_cons,List.count_nil] at hh hm
    apply h1.2.1 w
    · intro ha; have hma := List.count_pos_iff.mpr ha; omega
    · intro he; subst w; simp only [beq_self_eq_true,if_true] at hh; omega
  have keepReg (r : List Wire) (hr : r⊆x++y++L.history++L.work) : regValue r s1.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hw' => keep1 w (hr hw'))
  have h2 := montRestoreRounds_correct L x y p k X Y hw hnd hx hy hk hp hp16 hX s1 m1
    ((keepReg x (by intro w hh; simp [hh])).trans vx) ((keepReg y (by intro w hh; simp [hh])).trans vy)
    h1.2.2.1 ((keepReg L.history (by intro w hh; simp [hh])).trans vh)
    ((keepReg L.work (by intro w hh; simp [hh])).trans vw)
  rw [run_append,run_take]
  refine ⟨h2.1.trans h1.1,fun w ha hh hf => (h2.2.1 w ha hh).trans (h1.2.1 w ha hf),h2.2.2.1,h2.2.2.2,?_⟩
  have hout := List.disjoint_left.mp (L.inputs_disjoint x y hnd) (show L.flag∈x++y++[L.flag]++L.work by simp)
  exact (h2.2.1 L.flag (fun h => hout (by simp [h])) (fun h => hout (by simp [h]))).trans h1.2.2.2

private theorem montRestorePrefix_spec (L : MontStageLayout) (x y : List Wire) (p k X Y : Nat)
    (hw : L.Widths) (hnd : (x++y++L.wires).Nodup) (hx : 256≤x.length) (hy : 256≤y.length)
    (hk : k≤64) (hp : p<2^256) (hp16 : p%16=15) (hX : X<p) :
    {{ x=X,y=Y,L.acc=montgomeryValue p X Y k%p,L.history=montgomeryQuotient p X Y k,
       L.flag=decide (montgomeryValue p X Y k<p),L.work=0 }} (montDenormalize L p ++ montRestoreRounds L x y p k)
    {{ x=X,y=Y,L.acc=0,L.history=0,L.flag=false,L.work=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  rcases h with ⟨⟨⟨⟨⟨vx,vy⟩,va⟩,vh⟩,vf⟩,vw⟩
  have hh := montRestorePrefix_correct L x y p k X Y hw hnd hx hy hk hp hp16 hX s m vx vy va vh vf vw
  have hd := L.stable_disjoint x y hnd
  have keep (r : List Wire) (hr : r⊆x++y++L.work) : regValue r (run ((montDenormalize L p ++ montRestoreRounds L x y p k)) m s).basis=regValue r s.basis := by
    apply regValue_congr; intro w hw'
    have hn := List.disjoint_left.mp hd (hr hw')
    exact hh.2.1 w (fun hm => hn (by simp [hm])) (fun hm => hn (by simp [hm])) (fun he => hn (by simp [he]))
  exact ⟨hh.1,⟨⟨⟨⟨(keep x (by intro w hw'; simp [hw'])).trans vx,
    (keep y (by intro w hw'; simp [hw'])).trans vy⟩,hh.2.2.1⟩,hh.2.2.2.1⟩,hh.2.2.2.2⟩,
    (keep L.work (by intro w hw'; simp [hw'])).trans vw⟩

theorem montRestore_correct (L : MontStageLayout) (x y : List Wire) (p X Y : Nat)
    (hw : L.Widths) (hnd : (x++y++L.wires).Nodup) (hx : 256≤x.length) (hy : 256≤y.length)
    (hp : p<2^256) (hp16 : p%16=15) (hX : X<p)
    (s : State) (m : List Bool) (vx : regValue x s.basis=X) (vy : regValue y s.basis=Y)
    (va : regValue L.acc s.basis=montgomeryValue p X Y 64%p) (vh : regValue L.history s.basis=montgomeryQuotient p X Y 64)
    (vf : s.basis L.flag=decide (montgomeryValue p X Y 64<p)) (vw : regValue L.work s.basis=0) :
    (run (montRestore L x y p) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w∉L.history → w≠L.flag → (run (montRestore L x y p) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montRestore L x y p) m s).basis=0 ∧
    regValue L.history (run (montRestore L x y p) m s).basis=0 ∧
    (run (montRestore L x y p) m s).basis L.flag=false := by
  simpa only [montRestore] using montRestorePrefix_correct L x y p 64 X Y hw hnd hx hy (by omega) hp hp16 hX s m vx vy va vh vf vw

theorem montRestore_spec (L : MontStageLayout) (x y : List Wire) (p X Y : Nat)
    (hw : L.Widths) (hnd : (x++y++L.wires).Nodup) (hx : 256≤x.length) (hy : 256≤y.length)
    (hp : p<2^256) (hp16 : p%16=15) (hX : X<p) :
    {{ x=X,y=Y,L.acc=montgomeryValue p X Y 64%p,L.history=montgomeryQuotient p X Y 64,
       L.flag=decide (montgomeryValue p X Y 64<p),L.work=0 }} montRestore L x y p
    {{ x=X,y=Y,L.acc=0,L.history=0,L.flag=false,L.work=0 }} := by
  simpa only [montRestore] using montRestorePrefix_spec L x y p 64 X Y hw hnd hx hy (by omega) hp hp16 hX

end ECDSAAdd.Arithmetic
