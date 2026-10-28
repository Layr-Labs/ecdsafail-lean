import ECDSAAdd.Arithmetic.BalancedCoreCircuitProof

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField BalancedFold

theorem compose_raw_away (L : Layout) (hn : L.wires.Nodup) (a : Wire)
    (ha : a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
    a∉rawTarget L := by
  have nd : (rawTarget L++([L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [Layout.wires,BalancedCleanup.Layout.wires,rawTarget,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  exact fun h => List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 h ha

theorem compose_fold_subset (L : Layout) (a : Wire) (ha : a∉rawTarget L) : a∉foldTarget L := by
  have shape : rawTarget L=L.r0::foldTarget L := by
    simp [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  exact fun h => ha (by rw [shape]; exact List.mem_cons_of_mem _ h)

theorem compose_clean_views (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈[L.cout,L.minus,L.plus,L.lower]++L.carry) :
    q∉rawTarget L ∧ q≠L.sourceGuard ∧ q≠L.parity ∧ q∈work L := by
  have qa := compose_raw_away L hn q (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have ng : q≠L.sourceGuard := by
    rcases List.mem_append.mp hq with hq|hq
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> exact Ne.symm (by tauto)
    · intro e
      have hsg : L.sourceGuard∈L.carry := e ▸ hq
      exact flagAway L hn L.sourceGuard (by simp) (by simp [hsg])
  have np : q≠L.parity := by
    rcases List.mem_append.mp hq with hq|hq
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> tauto
    · intro e
      have hp : L.parity∈L.carry := e ▸ hq
      exact flagAway L hn L.parity (by simp) (by simp [hp])
  exact ⟨qa,ng,np,by
    simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto⟩

theorem compose_not_raw (L : Layout) (hn : L.wires.Nodup) (a : Wire)
    (ha : a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]) :
    a∉rawTarget L := by
  have data := flagAway L hn a (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ⊢; tauto)
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have no : a≠L.one := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all
  simp only [rawTarget,List.mem_append,List.mem_singleton,not_or]
  exact ⟨fun h => data (by simp [h]),no⟩

theorem compose_not_fold_r0 (L : Layout) (hn : L.wires.Nodup) : L.r0∉foldTarget L := by
  have nd := rawTargetND L hn
  simpa [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
    List.append_assoc] using (List.nodup_cons.mp (show (L.r0::foldTarget L).Nodup by
      simpa [rawTarget,foldTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
        List.append_assoc] using nd)).1

theorem compose_seed_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hc : ∀q∈work L,s.basis q=false) :
    (run (seedViews L) m s).phase=s.phase ∧
    (run (seedViews L) m s).basis L.sourceGuard=s.basis L.ymsb ∧
    ∀a,a≠L.sourceGuard → a≠L.one → a≠L.parity →
      (run (seedViews L) m s).basis a=s.basis a := by
  rw [seedViews_run L hw hn s m (hc _ (by simp [work]))
    (hc _ (by simp [work])) (hc _ (by simp [work]))]
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  refine ⟨rfl,?_,?_⟩
  · simp_all [writeBit,Function.update]
  · intro a h1 h2 h3
    simp only [writeBit,Function.update_of_ne h1,Function.update_of_ne h2,
      Function.update_of_ne h3]

theorem compose_prepare_bits (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (ho : s.basis L.one=N)
    (hr : s.basis L.r0=P) (hl : s.basis L.lower=false)
    (hm : s.basis L.minus=false) (hu : s.basis L.plus=false) :
    let t := run (prepareFold L) m s
    t.phase=s.phase ∧ t.basis L.r0=false ∧ t.basis L.lower=N ∧
    t.basis L.minus=(P && N) ∧ t.basis L.plus=(P && !N) ∧
    ∀a,a≠L.r0 → a≠L.one → a≠L.lower → a≠L.minus → a≠L.plus →
      t.basis a=s.basis a := by
  dsimp only
  rw [prepareFold_run L hn P N s m hp ho hr hl hm hu]
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have lm : L.lower≠L.minus := Ne.symm (by tauto)
  have lp : L.lower≠L.plus := Ne.symm (by tauto)
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · simp only [writeBit,Function.update_self]
  · simp_all [writeBit,Function.update]
  · simp_all [writeBit,Function.update]
  · simp_all [writeBit,Function.update]
  · intro a h1 h2 h3 h4 h5
    simp only [writeBit,Function.update_of_ne h1,Function.update_of_ne h2,
      Function.update_of_ne h3,Function.update_of_ne h4,Function.update_of_ne h5]

theorem compose_prepare_frame (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (ho : s.basis L.one=N)
    (hr : s.basis L.r0=P) (hl : s.basis L.lower=false)
    (hm : s.basis L.minus=false) (hu : s.basis L.plus=false) (a : Wire)
    (ha : a∉rawTarget L) (ha1 : a≠L.lower) (ha2 : a≠L.minus) (ha3 : a≠L.plus) :
    (run (prepareFold L) m s).basis a=s.basis a := by
  have h := compose_prepare_bits L hn P N s m hp ho hr hl hm hu
  exact h.2.2.2.2.2 a (fun e => ha (e ▸ (by simp [rawTarget,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])))
    (fun e => ha (e ▸ (by simp [rawTarget]))) ha1 ha2 ha3

theorem compose_release_frame (L : Layout) (hn : L.wires.Nodup) (P H : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (hh : s.basis L.rmsb=H)
    (hl : s.basis L.lower=(H ^^ P)) (hm : s.basis L.minus=(P && !H))
    (hu : s.basis L.plus=(P ^^ (P && !H))) :
    let t := run (releaseSelectors L) m s
    t.phase=s.phase ∧ t.basis L.lower=false ∧ t.basis L.minus=false ∧
    t.basis L.plus=false ∧ ∀a,a≠L.lower → a≠L.minus → a≠L.plus →
      t.basis a=s.basis a := by
  dsimp only
  rw [releaseSelectors_run L hn P H s m hp hh hl hm hu]
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have lm : L.lower≠L.minus := Ne.symm (by tauto)
  have lp : L.lower≠L.plus := Ne.symm (by tauto)
  have pm : L.plus≠L.minus := Ne.symm (by tauto)
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp_all [writeBit,Function.update]
  · simp only [writeBit,Function.update_self]
  · simp_all [writeBit,Function.update]
  · intro a h1 h2 h3
    simp only [writeBit,Function.update_of_ne h1,Function.update_of_ne h2,
      Function.update_of_ne h3]

end ECDSAAdd.Arithmetic.BalancedCircuit

#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.compose_prepare_bits
