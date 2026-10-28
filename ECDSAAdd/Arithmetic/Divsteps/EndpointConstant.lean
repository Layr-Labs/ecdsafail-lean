import ECDSAAdd.Arithmetic.Divsteps.ScaleRemoval

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Reuse the unary accumulator's mask for a controlled canonical constant.
The source is uncomputed after modular addition; no new register is allocated. -/
def endpointConstant (c : Wire) (U : ModUnaryLayout) (p k : Nat) : Program :=
  maskedConstant c U.mask k ++ modAddCore U.core p ++ maskedConstant c U.mask k

/-- A controlled constant update on the same accumulator used by reverseHalf.
Every nonoutput bit, including control, mask, flag and carry, is restored. -/
theorem endpointConstant_run (c : Wire) (U : ModUnaryLayout) (n p k r : Nat)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup)
    (hp : 0<p) (hpn : p<2^n) (hk : k<p) (hr : r<p)
    (s : State) (m : List Bool) (hz : regValue U.z s.basis=r)
    (hwork : regValue U.work s.basis=0) :
    let out := run (endpointConstant c U p k) m s
    out.phase=s.phase ∧ regValue U.z out.basis=(r+(if s.basis c then k else 0))%p ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  have hu := (List.nodup_cons.mp hnd).2
  have hm : U.mask.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hu q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,List.count_append,List.count_cons,List.count_nil] at hh
    omega
  have hc : c∉U.mask := by
    intro hh
    exact (List.nodup_cons.mp hnd).1 (by simp [ModUnaryLayout.wires,ModUnaryLayout.work,hh])
  have away (q : Wire) (hq : q∈U.z++U.core.work) : q∉U.mask := by
    intro hqm
    have hh := List.nodup_iff_count.mp hu q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hqm
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,List.count_append,List.count_cons,List.count_nil] at hh h1
    omega
  have cz : c∉U.z := by
    intro hh
    exact (List.nodup_cons.mp hnd).1 (List.mem_append_left _ hh)
  have clean := (regValue_zero U.work s.basis).mp hwork
  have hm0 : regValue U.mask s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => clean q (by simp [ModUnaryLayout.work,hq]))
  have hw0 : regValue U.core.work s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => clean q (by simp [ModUnaryLayout.work,hq]))
  have kb : k<2^U.mask.length := by rw [hw.mask,Nat.pow_succ]; omega
  let load := maskedConstant c U.mask k
  let t := run load m s
  let rmask := if s.basis c then k else 0
  let v := run (modAddCore U.core p) m t
  let out := run load (m.drop (measurementCount (modAddCore U.core p))) v
  have ht := maskedConstant_correct c U.mask k hm hc kb s m
  have htm : regValue U.core.a t.basis=rmask := by simpa [t,load,ModUnaryLayout.core,hm0,rmask] using ht.2.2
  have htc : t.basis c=s.basis c := ht.2.1 c hc
  have htz : regValue U.core.z t.basis=r :=
    (regValue_congr _ _ _ (fun q hq => ht.2.1 q (away q (List.mem_append_left _ hq)))).trans hz
  have htw : regValue U.core.work t.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ht.2.1 q (away q (List.mem_append_right _ hq)))).trans hw0
  have hmask : rmask≤p := by dsimp [rmask]; split <;> omega
  have hv := modAddCore_spec U.core n p rmask r (U.core_widths n hw) (U.core_nodup hu)
    hp hpn hmask hr t m ⟨⟨htm,htz⟩,htw⟩
  have vf (q : Wire) (hq : q∉U.z) : v.basis q=t.basis q :=
    modAddCore_frame U.core n p rmask r (U.core_widths n hw) (U.core_nodup hu)
      hp hpn hmask hr t m htm htz htw q hq
  have hvc : v.basis c=s.basis c := (vf c cz).trans htc
  have hvm : regValue U.mask v.basis=rmask := hv.2.1.1
  have ho := maskedConstant_correct c U.mask k hm hc kb v
    (m.drop (measurementCount (modAddCore U.core p)))
  have hom : regValue U.mask out.basis=0 := by simpa [out,load,hvm,hvc,rmask] using ho.2.2
  have hof (q : Wire) (hq : q∉U.z) : out.basis q=s.basis q := by
    by_cases hqm : q∈U.mask
    · exact ((regValue_zero _ _).mp hom q hqm).trans ((regValue_zero _ _).mp hm0 q hqm).symm
    · exact (ho.2.1 q hqm).trans ((vf q hq).trans (ht.2.1 q hqm))
  have hov : regValue U.z out.basis=(r+rmask)%p := by
    have hh := (regValue_congr _ _ _ (fun q hq => ho.2.1 q (away q (List.mem_append_left _ hq)))).trans hv.2.1.2
    simpa [Nat.add_comm] using hh
  have how : regValue U.work out.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have hd := (List.nodup_append'.mp hu).2.2
    exact (hof q (fun hz => List.disjoint_left.mp hd hz hq)).trans (clean q hq)
  have he : run (endpointConstant c U p k) m s=out := by
    rw [endpointConstant,run_append,run_take,run_append,run_take]
    simp only [(maskedConstant_counts c U.mask k).2,List.drop_zero,measurementCount_append,Nat.zero_add]
    rfl
  rw [he]
  exact ⟨ho.1.trans (hv.1.trans ht.1),hov,how,hof⟩

theorem endpointConstant_counts (c : Wire) (U : ModUnaryLayout) (n p k : Nat)
    (hw : U.Widths n) (hn : 0<n) :
    toffoliCount (endpointConstant c U p k)=4*n-1 ∧
    measurementCount (endpointConstant c U p k)=4*n-1 := by
  have hh := modAddCore_counts U.core n p (U.core_widths n hw) hn
  simp only [endpointConstant,toffoliCount_append,measurementCount_append,
    (maskedConstant_counts c U.mask k).1,(maskedConstant_counts c U.mask k).2,hh.1,hh.2]
  omega

theorem endpointConstant_support (c : Wire) (U : ModUnaryLayout) (n p k : Nat)
    (hw : U.Widths n) (hn : 0<n) :
    wires (endpointConstant c U p k)⊆(c::U.wires).toFinset := by
  have hm := maskedConstant_wires_subset c U.mask k
  have hc := modAddCore_wires U.core n p (U.core_widths n hw) hn
  have hm' : wires (maskedConstant c U.mask k)⊆(c::U.wires).toFinset := by
    intro q hq
    have hh := hm hq
    simp only [List.mem_toFinset,List.mem_cons] at hh
    simp only [List.mem_toFinset,List.mem_cons,ModUnaryLayout.wires,ModUnaryLayout.work,List.mem_append]
    tauto
  have hc' : wires (modAddCore U.core p)⊆(c::U.wires).toFinset := by
    rw [hc]
    intro q hq
    simp only [List.mem_toFinset,ModAddCoreLayout.wires,ModUnaryLayout.core,List.mem_append] at hq
    simp only [List.mem_toFinset,List.mem_cons,ModUnaryLayout.wires,ModUnaryLayout.work,List.mem_append]
    tauto
  simpa only [endpointConstant,wires_append,Finset.union_subset_iff] using And.intro (And.intro hm' hc') hm'

/-- Canonical weighted source bits, scanned without changing their wires. -/
def endpointWeighted (U : ModUnaryLayout) (p : Nat) (terms : List (Wire × Nat)) : Program :=
  terms.flatMap fun t => endpointConstant t.1 U p t.2

def endpointWeightedValue (terms : List (Wire × Nat)) (s : BasisState) : Nat :=
  (terms.map fun t => if s t.1 then t.2 else 0).sum

theorem endpointWeighted_run (U : ModUnaryLayout) (n p r : Nat) (terms : List (Wire × Nat))
    (hw : U.Widths n) (hnd : ∀ t∈terms,(t.1::U.wires).Nodup)
    (hp : 0<p) (hpn : p<2^n) (hk : ∀ t∈terms,t.2<p) (hr : r<p)
    (s : State) (m : List Bool) (hz : regValue U.z s.basis=r)
    (hwork : regValue U.work s.basis=0) :
    let out := run (endpointWeighted U p terms) m s
    out.phase=s.phase ∧ regValue U.z out.basis=(r+endpointWeightedValue terms s.basis)%p ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  induction terms generalizing r s m with
  | nil => simp [endpointWeighted,endpointWeightedValue,run,Nat.mod_eq_of_lt hr,hz,hwork]
  | cons term terms ih =>
    let v := run (endpointConstant term.1 U p term.2) m s
    let r' := (r+(if s.basis term.1 then term.2 else 0))%p
    have hv := endpointConstant_run term.1 U n p term.2 r hw (hnd term (by simp))
      hp hpn (hk term (by simp)) hr s m hz hwork
    have hh := ih r' (fun t ht => hnd t (by simp [ht])) (fun t ht => hk t (by simp [ht]))
      (Nat.mod_lt _ hp) v (m.drop (measurementCount (endpointConstant term.1 U p term.2))) hv.2.1 hv.2.2.1
    have he : endpointWeightedValue terms v.basis=endpointWeightedValue terms s.basis := by
      unfold endpointWeightedValue
      congr 1
      apply List.map_congr_left
      intro t ht
      have hc : t.1∉U.z := fun htz => (List.nodup_cons.mp (hnd t (by simp [ht]))).1
        (List.mem_append_left _ htz)
      rw [show v.basis t.1=s.basis t.1 from hv.2.2.2 _ hc]
    dsimp only
    rw [endpointWeighted,List.flatMap_cons,run_append,run_take]
    refine ⟨hh.1.trans hv.1,?_,hh.2.2.1,?_⟩
    · calc
        _ = (r'+endpointWeightedValue terms v.basis)%p := hh.2.1
        _ = _ := by
          rw [he]
          simp only [r',endpointWeightedValue,List.map_cons,List.sum_cons]
          simp only [Nat.mod_add_mod,Nat.add_assoc]
    · intro q hq
      exact (hh.2.2.2 q hq).trans (hv.2.2.2 q hq)

theorem endpointWeighted_counts (U : ModUnaryLayout) (n p : Nat) (terms : List (Wire × Nat))
    (hw : U.Widths n) (hn : 0<n) :
    toffoliCount (endpointWeighted U p terms)=terms.length*(4*n-1) ∧
    measurementCount (endpointWeighted U p terms)=terms.length*(4*n-1) := by
  induction terms with
  | nil => simp [endpointWeighted,toffoliCount,measurementCount]
  | cons t ts ih =>
    simp only [endpointWeighted,List.flatMap_cons,toffoliCount_append,measurementCount_append,
      (endpointConstant_counts t.1 U n p t.2 hw hn).1,
      (endpointConstant_counts t.1 U n p t.2 hw hn).2,List.length_cons] at *
    rw [ih.1,ih.2]
    constructor <;> ring

theorem endpointWeighted_support (U : ModUnaryLayout) (n p : Nat) (terms : List (Wire × Nat))
    (hw : U.Widths n) (hn : 0<n) :
    wires (endpointWeighted U p terms)⊆(terms.map Prod.fst++U.wires).toFinset := by
  induction terms with
  | nil => simp [endpointWeighted,wires]
  | cons t ts ih =>
    rw [endpointWeighted,List.flatMap_cons,wires_append,Finset.union_subset_iff]
    constructor
    · apply (endpointConstant_support t.1 U n p t.2 hw hn).trans
      intro q hq
      simp only [List.mem_toFinset,List.mem_cons] at hq
      simp only [List.map_cons,List.cons_append,List.mem_toFinset,List.mem_cons,List.mem_append]
      tauto
    · apply ih.trans
      intro q hq
      simpa only [List.map_cons,List.cons_append,List.toFinset_cons,Finset.mem_insert] using Or.inr hq

end ECDSAAdd.Arithmetic.Divsteps
