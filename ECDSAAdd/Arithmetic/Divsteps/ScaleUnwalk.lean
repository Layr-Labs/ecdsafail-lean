import ECDSAAdd.Arithmetic.Divsteps.PhysicalScale
import ECDSAAdd.Framework.MeasuredLocality

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- The inverse walk restores every non-accumulator bit after physical scale
removal. Its measured execution is compared on the walk support, not by
assuming that the scale stage is a full-state identity. -/
theorem StepLayout.unwalk_after_scale (L : StepLayout) (h : L.Valid)
    (p : Nat) (x : Int) (N : Nat) (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (U : ModUnaryLayout) (n r : Nat) (hw : U.Widths n)
    (hnd : ∀ c∈L.reverseActivityWires N,(c::U.wires).Nodup)
    (hsep : List.Disjoint U.wires L.used) (hp : p%2=1) (hpn : p<2^n) (hr : r<p)
    (s : State) (mf mr mi : List Bool) (hs : L.Ready (zSeed p x) s.basis)
    (hz : regValue U.z (run (L.walk N) mf s).basis=r)
    (hwork : regValue U.work (run (L.walk N) mf s).basis=0) :
    let t := run (L.walk N) mf s
    let u := run (L.reverseScale N U p) mr t
    let out := run (L.unwalk N) mi u
    out.phase=s.phase ∧ regValue U.z out.basis=halveActive p (reverseActivities p x N) r ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  let t := run (L.walk N) mf s
  let u := run (L.reverseScale N U p) mr t
  have hscale := L.reverseScale_from_walk h p x N hhistory hfit U n r hw hnd hp hpn hr
    s mf mr hs hz hwork
  have hzsep : List.Disjoint U.z L.used := (List.disjoint_append_left.mp hsep).1
  have hframe : ∀ q∈L.used.toFinset,u.basis q=t.basis q := by
    intro q hq
    exact hscale.2.2.2 q (fun hqz => List.disjoint_left.mp hzsep hqz (List.mem_toFinset.mp hq))
  have hlocal := run_measured_locality (L.unwalk N) L.used.toFinset
    (L.unwalk_support h N) u t mi hscale.1 hframe
  have hundo := L.unwalk_after h p x N hhistory hfit s mf mi hs
  change run (L.unwalk N) mi t=s at hundo
  rw [hundo] at hlocal
  have keep (q : Wire) (hq : q∈U.wires) : (run (L.unwalk N) mi u).basis q=u.basis q := by
    apply run_preserves_outside
    intro hq'
    exact List.disjoint_left.mp hsep hq (List.mem_toFinset.mp (L.unwalk_support h N hq'))
  have val (xs : List Wire) (hx : xs⊆U.wires) :
      regValue xs (run (L.unwalk N) mi u).basis=regValue xs u.basis := by
    apply (regValue_eq_iff _ _ _).mpr
    intro q hq
    exact keep q (hx hq)
  refine ⟨hlocal.1,?_,?_,?_⟩
  · exact (val U.z (List.subset_append_left _ _)).trans hscale.2.1
  · exact (val U.work (List.subset_append_right _ _)).trans hscale.2.2.1
  · intro q hqz
    by_cases hq : q∈L.used.toFinset
    · exact hlocal.2 q hq
    · have hu : (run (L.unwalk N) mi u).basis q=u.basis q :=
        run_preserves_outside _ _ _ _ (fun hh => hq (L.unwalk_support h N hh))
      have ht : t.basis q=s.basis q :=
        run_preserves_outside _ _ _ _ (fun hh => hq (L.walk_support h N hh))
      exact hu.trans ((hscale.2.2.2 q hqz).trans ht)

/-- Actual coherent walk, physical scale stage, then actual inverse walk. -/
def StepLayout.walkScaleUnwalk (L : StepLayout) (N : Nat) (U : ModUnaryLayout) (p : Nat) : Program :=
  L.walk N ++ L.reverseScale N U p ++ L.unwalk N

theorem StepLayout.walkScaleUnwalk_run (L : StepLayout) (h : L.Valid)
    (p : Nat) (x : Int) (N : Nat) (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (U : ModUnaryLayout) (n r : Nat) (hw : U.Widths n)
    (hnd : ∀ c∈L.reverseActivityWires N,(c::U.wires).Nodup)
    (hsep : List.Disjoint U.wires L.used) (hp : p%2=1) (hpn : p<2^n) (hr : r<p)
    (s : State) (m : List Bool) (hs : L.Ready (zSeed p x) s.basis)
    (hz : regValue U.z s.basis=r)
    (hwork : regValue U.work s.basis=0) :
    let out := run (L.walkScaleUnwalk N U p) m s
    out.phase=s.phase ∧ regValue U.z out.basis=halveActive p (reverseActivities p x N) r ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  have keep (q : Wire) (hq : q∈U.wires) : (run (L.walk N) m s).basis q=s.basis q := by
    apply run_preserves_outside
    intro hm
    exact List.disjoint_left.mp hsep hq (List.mem_toFinset.mp (L.walk_support h N hm))
  have val (xs : List Wire) (hx : xs⊆U.wires) :
      regValue xs (run (L.walk N) m s).basis=regValue xs s.basis := by
    apply (regValue_eq_iff _ _ _).mpr
    intro q hq
    exact keep q (hx hq)
  dsimp only
  rw [walkScaleUnwalk,run_append,run_take,run_append,run_take]
  exact L.unwalk_after_scale h p x N hhistory hfit U n r hw hnd hsep hp hpn hr
    s m _ _ hs ((val U.z (List.subset_append_left _ _)).trans hz)
      ((val U.work (List.subset_append_right _ _)).trans hwork)


theorem StepLayout.walkScaleUnwalk_counts (L : StepLayout) (h : L.Valid)
    (n v k N a p : Nat) (hw : L.Sized n v k) (U : ModUnaryLayout)
    (hu : U.Widths a) (ha : 0<a) :
    toffoliCount (L.walkScaleUnwalk N U p)=2*(N*(5*n+5*v+k-4))+N*(3*a+2) ∧
    measurementCount (L.walkScaleUnwalk N U p)=2*(N*(4*n+3*v+k-5))+N*(2*a) := by
  have hf := L.walk_counts h n v k N hw
  have hr := L.reverseScale_counts N U a p hu ha
  have hi := L.unwalk_counts h n v k N hw
  simp only [walkScaleUnwalk,toffoliCount_append,measurementCount_append,
    hf.1,hf.2,hr.1,hr.2,hi.1,hi.2]
  constructor <;> ring

theorem StepLayout.walkScaleUnwalk_support (L : StepLayout) (h : L.Valid)
    (N : Nat) (U : ModUnaryLayout) (n p : Nat) (hw : U.Widths n) (hn : 0<n) :
    wires (L.walkScaleUnwalk N U p)⊆(L.used++U.wires).toFinset := by
  change wires (L.walkAndScale N U p ++ L.unwalk N)⊆_
  rw [wires_append,Finset.union_subset_iff]
  refine ⟨L.walkAndScale_support h N U n p hw hn,?_⟩
  intro q hq
  simp only [List.toFinset_append,Finset.mem_union]
  exact Or.inl (L.unwalk_support h N hq)

theorem StepLayout.walkScaleUnwalk_qubits (L : StepLayout) (h : L.Valid)
    (N : Nat) (U : ModUnaryLayout) (n p : Nat) (hw : U.Widths n) (hn : 0<n) :
    qubitCount (L.walkScaleUnwalk N U p)≤L.used.length+U.wires.length := by
  have hh := (Finset.card_le_card (L.walkScaleUnwalk_support h N U n p hw hn)).trans
    (List.toFinset_card_le (L.used++U.wires))
  simpa only [qubitCount,List.length_append] using hh

/-- Conditional field output plus exact restoration of every non-output bit
for the same complete measured program. The scaled input and first stopping
index are explicit premises, not inferred from the round-trip construction. -/
theorem StepLayout.walkScaleUnwalk_remove_scale (L : StepLayout) (h : L.Valid)
    (p x N t r : Nat) [Fact p.Prime] (target : ZMod p) (hhistory : N≤L.future.length)
    (hfit : ∀ i, i<N → (L.at i).Fits (zWalk p x i))
    (U : ModUnaryLayout) (n : Nat) (hw : U.Widths n)
    (hnd : ∀ c∈L.reverseActivityWires N,(c::U.wires).Nodup)
    (hsep : List.Disjoint U.wires L.used) (hp : p%2=1) (hpn : p<2^n) (hr : r<p)
    (h2 : (2 : ZMod p)≠0) (ht : t≤N) (hstop : (zWalk p x t).g=0)
    (hbefore : ∀ i, i<t → (zWalk p x i).g≠0) (hscaled : (r : ZMod p)=target*2^t)
    (s : State) (m : List Bool) (hs : L.Ready (zSeed p x) s.basis)
    (hz : regValue U.z s.basis=r) (hwork : regValue U.work s.basis=0) :
    let out := run (L.walkScaleUnwalk N U p) m s
    (regValue U.z out.basis : ZMod p)=target ∧ out.phase=s.phase ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  have hh := L.walkScaleUnwalk_run h p x N hhistory hfit U n r hw hnd hsep hp hpn hr
    s m hs hz hwork
  refine ⟨?_,hh.1,hh.2.2⟩
  rw [hh.2.1]
  exact reverseWalk_remove_scale p x N t r target hp hr h2 ht hstop hbefore hscaled

theorem StepLayout.walkScaleUnwalk590_counts (L : StepLayout) (h : L.Valid)
    (hw : L.Sized 258 592 11) (U : ModUnaryLayout) (hu : U.Widths 256) (p : Nat) :
    toffoliCount (L.walkScaleUnwalk 590 U p)=5477560 ∧
    measurementCount (L.walkScaleUnwalk 590 U p)=3622600 := by
  have hh := L.walkScaleUnwalk_counts h 258 592 11 590 256 p hw U hu (by decide)
  norm_num at hh
  exact hh


theorem StepLayout.reverseScale_controls_nodup (L : StepLayout) (N : Nat) (U : ModUnaryLayout)
    (hu : U.wires.Nodup) (hsep : List.Disjoint U.wires L.used) :
    ∀ c∈L.reverseActivityWires N,(c::U.wires).Nodup := by
  intro c hc
  apply List.nodup_cons.mpr
  refine ⟨?_,hu⟩
  intro hcu
  exact List.disjoint_left.mp hsep hcu (List.mem_toFinset.mp
    (L.reverseActivityWires_support N (List.mem_toFinset.mpr hc)))

/-- All numeric walk fits are discharged for canonical 256-bit inputs. The
result is exact controlled halving and restoration without a termination
assumption; identifying a division output still requires the scale relation. -/
theorem StepLayout.walkScaleUnwalk590_run (L : StepLayout) (h : L.Valid)
    (hw : L.Sized 258 592 11) (hhistory : 590≤L.future.length)
    (p x r : Nat) (hp : p%2=1) (hsmall : p<2^256) (hxp : x≤p) (hr : r<p)
    (U : ModUnaryLayout) (hu : U.Widths 256) (hund : U.wires.Nodup)
    (hsep : List.Disjoint U.wires L.used) (s : State) (m : List Bool)
    (hs : L.Ready (zSeed p x) s.basis) (hz : regValue U.z s.basis=r)
    (hwork : regValue U.work s.basis=0) :
    let out := run (L.walkScaleUnwalk 590 U p) m s
    out.phase=s.phase ∧ regValue U.z out.basis=halveActive p (reverseActivities p x 590) r ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  have hfit := L.walk590_fits hw p x (by omega) (by exact_mod_cast hp)
    (by exact_mod_cast hsmall) (by omega) (by exact_mod_cast hxp)
  exact L.walkScaleUnwalk_run h p x 590 hhistory hfit U 256 r hu
    (L.reverseScale_controls_nodup 590 U hund hsep) hsep hp hsmall hr s m hs hz hwork

end ECDSAAdd.Arithmetic.Divsteps
