import ECDSAAdd.Arithmetic.Divsteps.WalkActivity

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- Execute modular halvings in the supplied physical control order. -/
def reverseHalves (controls : List Wire) (U : ModUnaryLayout) (p : Nat) : Program :=
  controls.flatMap (fun c => reverseHalf c U p)

theorem reverseHalves_run (controls : List Wire) (U : ModUnaryLayout) (n p r : Nat)
    (hw : U.Widths n) (hnd : ∀ c∈controls,(c::U.wires).Nodup)
    (hp : p%2=1) (hpn : p<2^n) (hr : r<p) (s : State) (m : List Bool)
    (hz : regValue U.z s.basis=r) (hwork : regValue U.work s.basis=0) :
    let out := run (reverseHalves controls U p) m s
    out.phase=s.phase ∧ regValue U.z out.basis=halveActive p (controls.map s.basis) r ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  induction controls generalizing r s m with
  | nil => exact ⟨rfl,hz,hwork,by intro q _; rfl⟩
  | cons c cs ih =>
    let t := run (reverseHalf c U p) m s
    let r' := if s.basis c then halveMod p r else r
    have hhead := reverseHalf_spec c U n p r (s.basis c) hw (hnd c (by simp)) hp hpn hr
      s m ⟨⟨rfl,hz⟩,hwork⟩
    have hr' : r'<p := by
      dsimp [r']
      split <;> first | exact halve_mod_bound p r hp hr | exact hr
    have frame (q : Wire) (hq : q∉U.z) : t.basis q=s.basis q :=
      controlledHalf_frame c U n p r (s.basis c) hw (hnd c (by simp)) hp hpn hr
        s m rfl hz hwork q hq
    have hv : cs.map t.basis=cs.map s.basis := by
      apply List.map_congr_left
      intro q hq
      apply frame
      intro hqz
      exact (List.nodup_cons.mp (hnd q (by simp [hq]))).1
        (List.mem_append_left _ hqz)
    have ht := ih r' (fun q hq => hnd q (by simp [hq])) hr' t
      (m.drop (measurementCount (reverseHalf c U p))) hhead.2.1.2 hhead.2.2
    dsimp only at ht ⊢
    rw [reverseHalves,List.flatMap_cons,run_append,run_take]
    change (run (reverseHalves cs U p) _ t).phase=s.phase ∧ _
    refine ⟨ht.1.trans hhead.1,?_,ht.2.2.1,?_⟩
    · simpa only [hv,List.map_cons,halveActive] using ht.2.1
    · intro q hq
      exact (ht.2.2.2 q hq).trans (frame q hq)

theorem reverseHalves_counts (controls : List Wire) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hn : 0<n) :
    toffoliCount (reverseHalves controls U p)=controls.length*(3*n+2) ∧
    measurementCount (reverseHalves controls U p)=controls.length*(2*n) := by
  induction controls with
  | nil => simp [reverseHalves,toffoliCount,measurementCount]
  | cons c cs ih =>
    have hh := reverseHalf_counts c U n p hw hn
    simp only [reverseHalves,List.flatMap_cons,toffoliCount_append,measurementCount_append,
      hh.1,hh.2,List.length_cons] at *
    constructor <;> nlinarith [ih.1,ih.2]

theorem reverseHalves_support (controls : List Wire) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hn : 0<n) :
    wires (reverseHalves controls U p)⊆(controls++U.wires).toFinset := by
  induction controls with
  | nil => simp [reverseHalves,wires]
  | cons c cs ih =>
    rw [reverseHalves,List.flatMap_cons,wires_append]
    rw [reverseHalf_wires c U n p hw hn]
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,ModUnaryLayout.wires,
        ModUnaryLayout.work]
      tauto
    · have hh := ih hq
      simpa only [List.cons_append,List.mem_toFinset,List.mem_cons] using Or.inr hh

/-- The physical scale stage reads the controls written by the forward walk,
in reverse order. It allocates no activity counter. -/
def StepLayout.reverseScale (L : StepLayout) (N : Nat) (U : ModUnaryLayout) (p : Nat) : Program :=
  reverseHalves (L.reverseActivityWires N) U p

theorem StepLayout.reverseScale_from_walk (L : StepLayout) (h : L.Valid)
    (p : Nat) (x : Int) (N : Nat) (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (U : ModUnaryLayout) (n r : Nat) (hw : U.Widths n)
    (hnd : ∀ c∈L.reverseActivityWires N,(c::U.wires).Nodup)
    (hp : p%2=1) (hpn : p<2^n) (hr : r<p) (s : State) (mf mr : List Bool)
    (hs : L.Ready (zSeed p x) s.basis)
    (hz : regValue U.z (run (L.walk N) mf s).basis=r)
    (hwork : regValue U.work (run (L.walk N) mf s).basis=0) :
    let t := run (L.walk N) mf s
    let out := run (L.reverseScale N U p) mr t
    out.phase=t.phase ∧ regValue U.z out.basis=halveActive p (reverseActivities p x N) r ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=t.basis q := by
  have hh := reverseHalves_run (L.reverseActivityWires N) U n p r hw hnd hp hpn hr
    (run (L.walk N) mf s) mr hz hwork
  rw [L.reverseActivityWires_values h p x N hhistory hfit s mf hs] at hh
  exact hh


theorem StepLayout.reverseScale_counts (L : StepLayout) (N : Nat) (U : ModUnaryLayout)
    (n p : Nat) (hw : U.Widths n) (hn : 0<n) :
    toffoliCount (L.reverseScale N U p)=N*(3*n+2) ∧
    measurementCount (L.reverseScale N U p)=N*(2*n) := by
  simpa only [reverseScale,reverseActivityWires,List.length_reverse,List.length_map,List.length_range]
    using reverseHalves_counts (L.reverseActivityWires N) U n p hw hn

theorem StepLayout.reverseActivityWires_support (L : StepLayout) (N : Nat) :
    (L.reverseActivityWires N).toFinset⊆L.used.toFinset := by
  intro w hw
  simp only [List.mem_toFinset,reverseActivityWires,List.mem_reverse,List.mem_map] at hw
  obtain ⟨i,_,rfl⟩ := hw
  rw [←L.at_support i]
  simp [used,histories,StepHistory.wires]

theorem StepLayout.reverseScale_support (L : StepLayout) (N : Nat) (U : ModUnaryLayout)
    (n p : Nat) (hw : U.Widths n) (hn : 0<n) :
    wires (L.reverseScale N U p)⊆(L.used++U.wires).toFinset := by
  have hs := reverseHalves_support (L.reverseActivityWires N) U n p hw hn
  intro w hw'
  have hm := hs hw'
  simp only [List.toFinset_append,Finset.mem_union] at hm ⊢
  exact hm.elim (fun hh => Or.inl (L.reverseActivityWires_support N hh)) Or.inr

/-- Actual forward walk followed by physical inverse-order activity-controlled
halving. This stage does not yet execute the inverse walk. -/
def StepLayout.walkAndScale (L : StepLayout) (N : Nat) (U : ModUnaryLayout) (p : Nat) : Program :=
  L.walk N ++ L.reverseScale N U p

theorem StepLayout.walkAndScale_counts (L : StepLayout) (h : L.Valid)
    (n v k N a p : Nat) (hw : L.Sized n v k) (U : ModUnaryLayout)
    (hu : U.Widths a) (ha : 0<a) :
    toffoliCount (L.walkAndScale N U p)=N*(5*n+5*v+k-4)+N*(3*a+2) ∧
    measurementCount (L.walkAndScale N U p)=N*(4*n+3*v+k-5)+N*(2*a) := by
  have hf := L.walk_counts h n v k N hw
  have hr := L.reverseScale_counts N U a p hu ha
  simp only [walkAndScale,toffoliCount_append,measurementCount_append,hf.1,hf.2,hr.1,hr.2,and_self]

theorem StepLayout.walkAndScale_support (L : StepLayout) (h : L.Valid)
    (N : Nat) (U : ModUnaryLayout) (n p : Nat) (hw : U.Widths n) (hn : 0<n) :
    wires (L.walkAndScale N U p)⊆(L.used++U.wires).toFinset := by
  rw [walkAndScale,wires_append,Finset.union_subset_iff]
  refine ⟨?_,L.reverseScale_support N U n p hw hn⟩
  intro w hw'
  simp only [List.toFinset_append,Finset.mem_union]
  exact Or.inl (L.walk_support h N hw')

/-- Concrete gate-level scale removal driven by the activity bits proved to
have been written by the actual forward walk. The scaled endpoint and stopping
premises remain explicit; they are not inferred from a fixed slot count. -/
theorem StepLayout.walkAndScale_remove_scale (L : StepLayout) (h : L.Valid)
    (p x N t r : Nat) [Fact p.Prime] (target : ZMod p) (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (U : ModUnaryLayout) (n : Nat) (hw : U.Widths n)
    (hnd : ∀ c∈L.reverseActivityWires N,(c::U.wires).Nodup)
    (hp : p%2=1) (hpn : p<2^n) (hr : r<p) (h2 : (2 : ZMod p)≠0)
    (ht : t≤N) (hstop : (zWalk p x t).g=0) (hbefore : ∀ i, i<t → (zWalk p x i).g≠0)
    (hscaled : (r : ZMod p)=target*2^t) (s : State) (m : List Bool)
    (hs : L.Ready (zSeed p x) s.basis)
    (hz : regValue U.z (run (L.walk N) m s).basis=r)
    (hwork : regValue U.work (run (L.walk N) m s).basis=0) :
    (regValue U.z (run (L.walkAndScale N U p) m s).basis : ZMod p)=target ∧
    regValue U.work (run (L.walkAndScale N U p) m s).basis=0 ∧
    (run (L.walkAndScale N U p) m s).phase=s.phase := by
  have hh := L.reverseScale_from_walk h p x N hhistory hfit U n r hw hnd hp hpn hr
    s m (m.drop (measurementCount (L.walk N))) hs hz hwork
  have hf := (L.walk_spec h p x N hhistory hfit s m hs).1
  rw [walkAndScale,run_append,run_take]
  refine ⟨?_,hh.2.2.1,hh.1.trans hf⟩
  rw [hh.2.1]
  exact reverseWalk_remove_scale p x N t r target hp hr h2 ht hstop hbefore hscaled


/-- If the accumulator is disjoint from the walk allocation, scale removal
preserves every walk wire, including all retained history, for later uncompute. -/
theorem StepLayout.walkAndScale_frame (L : StepLayout) (h : L.Valid)
    (p : Nat) (x : Int) (N : Nat) (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (U : ModUnaryLayout) (n r : Nat) (hw : U.Widths n)
    (hnd : ∀ c∈L.reverseActivityWires N,(c::U.wires).Nodup)
    (hsep : List.Disjoint U.z L.used) (hp : p%2=1) (hpn : p<2^n) (hr : r<p)
    (s : State) (m : List Bool) (hs : L.Ready (zSeed p x) s.basis)
    (hz : regValue U.z (run (L.walk N) m s).basis=r)
    (hwork : regValue U.work (run (L.walk N) m s).basis=0) :
    ∀ q∈L.used, (run (L.walkAndScale N U p) m s).basis q=(run (L.walk N) m s).basis q := by
  have hh := L.reverseScale_from_walk h p x N hhistory hfit U n r hw hnd hp hpn hr
    s m (m.drop (measurementCount (L.walk N))) hs hz hwork
  intro q hq
  rw [walkAndScale,run_append,run_take]
  exact hh.2.2.2 q (fun hqz => List.disjoint_left.mp hsep hqz hq)

theorem StepLayout.walkAndScale_qubits (L : StepLayout) (h : L.Valid)
    (N : Nat) (U : ModUnaryLayout) (n p : Nat) (hw : U.Widths n) (hn : 0<n) :
    qubitCount (L.walkAndScale N U p)≤L.used.length+U.wires.length := by
  have hh := (Finset.card_le_card (L.walkAndScale_support h N U n p hw hn)).trans
    (List.toFinset_card_le (L.used++U.wires))
  simpa only [qubitCount,List.length_append] using hh

end ECDSAAdd.Arithmetic.Divsteps
