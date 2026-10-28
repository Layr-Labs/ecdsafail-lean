import ECDSAAdd.Arithmetic.MontWindow

namespace ECDSAAdd.Arithmetic

/-- k轮后，累加器和整条历史分别等于 a_k 与 Q_k。 -/
theorem montPrepareRounds_correct (L : MontStageLayout) (x y : List Wire) (p k X Y : Nat)
    (hw : L.Widths) (hnd : (x++y++L.wires).Nodup) (hx : 256≤x.length) (hy : 256≤y.length)
    (hk : k≤64) (hp : p<2^256) (hp16 : p%16=15) (hX : X<p)
    (s : State) (m : List Bool) (vx : regValue x s.basis=X) (vy : regValue y s.basis=Y)
    (va : regValue L.acc s.basis=0) (vh : regValue L.history s.basis=0) (vw : regValue L.work s.basis=0) :
    (run (montPrepareRounds L x y p k) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w∉L.history → (run (montPrepareRounds L x y p k) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montPrepareRounds L x y p k) m s).basis=montgomeryValue p X Y k ∧
    regValue L.history (run (montPrepareRounds L x y p k) m s).basis=montgomeryQuotient p X Y k := by
  induction k with
  | zero => exact ⟨rfl,fun _ _ _ => rfl,va,vh⟩
  | succ k ih =>
    let s1 := run (montPrepareRounds L x y p k) m s
    let m1 := m.drop (measurementCount (montPrepareRounds L x y p k))
    have h1 := ih (by omega)
    have ad := L.inputs_disjoint x y hnd
    have keep1 (r : List Wire) (hr : r⊆x++y++[L.flag]++L.work) : regValue r s1.basis=regValue r s.basis := by
      apply regValue_congr; intro w hw'
      have hh := List.disjoint_left.mp ad (hr hw')
      exact h1.2.1 w (fun hm => hh (List.mem_append_left _ hm)) (fun hm => hh (List.mem_append_right _ hm))
    have h2 := montWindow_correct L x y p k X Y (montgomeryValue p X Y k) (montgomeryQuotient p X Y k)
      hw hnd hx hy (by omega) hp hp16 hX (montgomeryValue_bound p X Y k hX) (montgomeryQuotient_bound p X Y k)
      s1 m1 ((keep1 x (by intro w hh; simp [hh])).trans vx)
      ((keep1 y (by intro w hh; simp [hh])).trans vy) h1.2.2.1 h1.2.2.2
      ((keep1 L.work (by intro w hh; simp [hh])).trans vw)
    rw [montPrepareRounds,run_append,run_take]
    exact ⟨h2.1.trans h1.1,fun w ha hh => (h2.2.1 w ha hh).trans (h1.2.1 w ha hh),h2.2.2.1,h2.2.2.2⟩

/-- 以同一 a_k/Q_k 关系为前提逆序执行，清空累加器与整条历史。 -/
theorem montRestoreRounds_correct (L : MontStageLayout) (x y : List Wire) (p k X Y : Nat)
    (hw : L.Widths) (hnd : (x++y++L.wires).Nodup) (hx : 256≤x.length) (hy : 256≤y.length)
    (hk : k≤64) (hp : p<2^256) (hp16 : p%16=15) (hX : X<p)
    (s : State) (m : List Bool) (vx : regValue x s.basis=X) (vy : regValue y s.basis=Y)
    (va : regValue L.acc s.basis=montgomeryValue p X Y k)
    (vh : regValue L.history s.basis=montgomeryQuotient p X Y k) (vw : regValue L.work s.basis=0) :
    (run (montRestoreRounds L x y p k) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → w∉L.history → (run (montRestoreRounds L x y p k) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montRestoreRounds L x y p k) m s).basis=0 ∧
    regValue L.history (run (montRestoreRounds L x y p k) m s).basis=0 := by
  induction k generalizing s m with
  | zero => exact ⟨rfl,fun _ _ _ => rfl,va,vh⟩
  | succ k ih =>
    let s1 := run (montRestoreWindow L x y p k) m s
    let m1 := m.drop (measurementCount (montRestoreWindow L x y p k))
    have h1 := montRestoreWindow_correct L x y p k X Y (montgomeryValue p X Y k) (montgomeryQuotient p X Y k)
      hw hnd hx hy (by omega) hp hp16 hX (montgomeryValue_bound p X Y k hX) (montgomeryQuotient_bound p X Y k)
      s m vx vy va vh vw
    have ad := L.inputs_disjoint x y hnd
    have keep1 (r : List Wire) (hr : r⊆x++y++[L.flag]++L.work) : regValue r s1.basis=regValue r s.basis := by
      apply regValue_congr; intro w hw'
      have hh := List.disjoint_left.mp ad (hr hw')
      exact h1.2.1 w (fun hm => hh (List.mem_append_left _ hm)) (fun hm => hh (List.mem_append_right _ hm))
    have h2 := ih (by omega) s1 m1 ((keep1 x (by intro w hh; simp [hh])).trans vx)
      ((keep1 y (by intro w hh; simp [hh])).trans vy) h1.2.2.1 h1.2.2.2
      ((keep1 L.work (by intro w hh; simp [hh])).trans vw)
    rw [montRestoreRounds,run_append,run_take]
    exact ⟨h2.1.trans h1.1,fun w ha hh => (h2.2.1 w ha hh).trans (h1.2.1 w ha hh),h2.2.2.1,h2.2.2.2⟩

end ECDSAAdd.Arithmetic
