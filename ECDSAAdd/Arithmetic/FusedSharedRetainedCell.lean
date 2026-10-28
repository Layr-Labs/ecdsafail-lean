import ECDSAAdd.Arithmetic.FusedSharedRetained
import ECDSAAdd.Arithmetic.FusedFieldBridge
import ECDSAAdd.Arithmetic.ReplayCellState

namespace ECDSAAdd.Arithmetic
open Secp256k1

def fusedSharedRetainedSignedHalf (w : Nat → Wire) (g : Wire) : Program :=
  fusedFieldSignedHalf g (fusedSharedPorts w g).compactForwardProgram

theorem fusedSharedRetainedSignedHalf_counts (w : Nat → Wire) (g : Wire) :
    toffoliCount (fusedSharedRetainedSignedHalf w g)=1538 ∧
    measurementCount (fusedSharedRetainedSignedHalf w g)=1538 :=
  fusedFieldSignedHalf_counts g (fusedSharedPorts w g).compactForwardProgram 1538 1538
    (fusedSharedRetainedKernel_counts w g)

theorem fusedSharedRetainedSignedHalf_correct (w : Nat → Wire) (g : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hg : g∉fusedSharedIds.map w)
    (hgf : (g::(skywalkSharedField w).wires).Nodup)
    (hgu : g∉skywalkSharedUnused w)
    (X Y : Nat) (hX : X<p) (hY : Y<p) (s : State) (record : List Bool)
    (hy : regValue (skywalkSharedField w).a s.basis=Y)
    (hx : regValue (skywalkSharedField w).z s.basis=X)
    (hk : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0) :
    (run (fusedSharedRetainedSignedHalf w g) record s).phase=s.phase ∧
    (∀ q,q∉(skywalkSharedField w).z →
      (run (fusedSharedRetainedSignedHalf w g) record s).basis q=s.basis q) ∧
    regValue (skywalkSharedField w).z
      (run (fusedSharedRetainedSignedHalf w g) record s).basis=
      (skywalkFieldNat p (s.basis g) false X Y).1 := by
  have hkernel : ∀ st : State, ∀ ms : List Bool,
      regValue (skywalkSharedField w).a st.basis=Y →
      regValue (skywalkSharedField w).z st.basis=X →
      regValue (skywalkSharedField w).work st.basis=0 →
      regValue (skywalkSharedUnused w) st.basis=0 →
      (run (fusedSharedPorts w g).compactForwardProgram ms st).phase=st.phase ∧
      (∀ q,q∉(skywalkSharedField w).z →
        (run (fusedSharedPorts w g).compactForwardProgram ms st).basis q=st.basis q) ∧
      regValue (skywalkSharedField w).z
        (run (fusedSharedPorts w g).compactForwardProgram ms st).basis=
        FusedSignedHalf.result p (st.basis g) X Y := by
    intro st ms hy' hx' hk' hu'
    exact fusedSharedRetainedKernel_correct w g hn hg X Y hX hY st ms hy' hx' hk' hu'
  unfold fusedSharedRetainedSignedHalf
  exact fusedFieldSignedHalf_correct (skywalkSharedField w) (skywalkSharedUnused w)
    g (fusedSharedPorts w g).compactForwardProgram X Y hX hY hgf hgu hkernel
    s record hy hx hk hu

/-- A forward retained-carry cell preserves the same public ReplayValues
interface and the four explicitly borrowed padding sites. -/
def FusedSharedReplayValues (active swap g : Wire) (w : Nat → Wire)
    (C S G : Bool) (X Y : Nat) (st : BasisState) : Prop :=
  ReplayValues active swap g (skywalkSharedField w) C S G X Y st ∧
  regValue (skywalkSharedUnused w) st=0

def fusedSharedRetainedCell (w : Nat → Wire) (g swap : Wire) : Program :=
  fusedSharedRetainedSignedHalf w g ++
  swapRegisters swap ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
    ((skywalkSharedField w).a.take (skywalkSharedField w).low.length)

private theorem swap_preserves_disjoint_reg (c : Wire) (a b r : List Wire)
    (hlen : a.length=b.length) (hc : c∉r) (ha : r.Disjoint a) (hb : r.Disjoint b)
    (s : State) (m : List Bool) :
    regValue r (run (swapRegisters c a b) m s).basis=regValue r s.basis := by
  have hs := swapRegisters_wires c a b hlen
  apply regValue_congr
  intro q hq
  apply run_preserves_outside
  intro hm
  have hh := List.mem_toFinset.mp (hs hm)
  simp only [List.mem_cons,List.mem_append] at hh
  rcases hh with he|hqa|hqb
  · exact hc (he ▸ hq)
  · exact List.disjoint_left.mp ha hq hqa
  · exact List.disjoint_left.mp hb hq hqb

theorem fusedSharedRetainedCell_spec (active swap g : Wire) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (hg : g∉fusedSharedIds.map w)
    (hnd : (active::swap::g::(skywalkSharedField w).wires).Nodup)
    (hgu : g∉skywalkSharedUnused w) (hsu : swap∉skywalkSharedUnused w)
    (X Y : Nat) (hX : X<p) (hY : Y<p) (C S G : Bool) :
    Triple (FusedSharedReplayValues active swap g w C S G X Y)
      (fusedSharedRetainedCell w g swap)
      (FusedSharedReplayValues active swap g w C S G
        (skywalkFieldNat p G S X Y).1 (skywalkFieldNat p G S X Y).2) := by
  have hw := skywalkShared_field_widths w
  have hgf := ReplayValues.control_nodup active swap g (skywalkSharedField w) hnd g (by simp)
  have hp0 : 0<p := p_prime.pos
  have hpo : p%2=1 := by norm_num [p]
  let A := (skywalkFieldNat p G false X Y).1
  have hA : A<p := by
    have hd : skywalkSignedNat p G X Y<p := by
      cases G <;> simp only [skywalkSignedNat,Bool.false_eq_true,if_false,if_true]
      all_goals exact Nat.mod_lt _ hp0
    simpa only [A,skywalkFieldNat,Bool.false_eq_true,if_false] using
      halve_mod_bound p _ hpo hd
  intro s m h
  rw [fusedSharedRetainedCell,run_append]
  generalize hfirst : run (fusedSharedRetainedSignedHalf w g)
    (m.take (measurementCount (fusedSharedRetainedSignedHalf w g))) s=first
  have h1 := fusedSharedRetainedSignedHalf_correct w g hn hg hgf hgu X Y hX hY
    s (m.take (measurementCount (fusedSharedRetainedSignedHalf w g)))
    h.1.2.2.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.2 h.2
  rw [hfirst] at h1
  have zaway (q : Wire) (hq : q∈(skywalkSharedField w).a++(skywalkSharedField w).work) : q∉(skywalkSharedField w).z := by
    intro hz
    have hc := List.nodup_iff_count.mp (skywalkShared_field_nodup w hn) q
    have hZ := List.count_pos_iff.mpr hz
    have hQ := List.count_pos_iff.mpr hq
    simp only [ModInPlaceLayout.wires,List.count_append] at hc
    simp only [List.count_append] at hQ
    omega
  have mid : ReplayValues active swap g (skywalkSharedField w) C S G A Y first.basis := by
    have hvalue : regValue (skywalkSharedField w).z first.basis=A := by
      rw [h1.2.2]
      exact congrArg (fun b => (skywalkFieldNat p b false X Y).1) h.1.2.2.1
    refine ⟨?_,?_,?_,hvalue,?_,?_⟩
    · exact (h1.2.1 active (ReplayValues.control_outside active swap g (skywalkSharedField w) hnd active (by simp)).1).trans h.1.1
    · exact (h1.2.1 swap (ReplayValues.control_outside active swap g (skywalkSharedField w) hnd swap (by simp)).1).trans h.1.2.1
    · exact (h1.2.1 g (ReplayValues.control_outside active swap g (skywalkSharedField w) hnd g (by simp)).1).trans h.1.2.2.1
    · exact (regValue_congr (skywalkSharedField w).a first.basis s.basis
        (fun q hq => h1.2.1 q (zaway q (List.mem_append_left _ hq)))).trans h.1.2.2.2.2.1
    · exact (regValue_congr (skywalkSharedField w).work first.basis s.basis
        (fun q hq => h1.2.1 q (zaway q (List.mem_append_right _ hq)))).trans h.1.2.2.2.2.2
  have h2 := ReplayValues.swap_step active swap g (skywalkSharedField w) 256 A Y C S G hw hnd
    (hA.trans (by norm_num [p])) (hY.trans (by norm_num [p])) first
    (m.drop (measurementCount (fusedSharedRetainedSignedHalf w g))) mid
  have hu1 : regValue (skywalkSharedUnused w) first.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => h1.2.1 q
      (fun hz => (skywalkShared_unused_outside w hn q hq) (by
        simp [ModInPlaceLayout.wires,hz])))).trans h.2
  have hlen : ((skywalkSharedField w).z.take (skywalkSharedField w).low.length).length=((skywalkSharedField w).a.take (skywalkSharedField w).low.length).length := by
    simp [List.length_take,ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hdisZ : (skywalkSharedUnused w).Disjoint
      ((skywalkSharedField w).z.take (skywalkSharedField w).low.length) := by
    apply List.disjoint_left.mpr
    intro q hq hz
    exact (skywalkShared_unused_outside w hn q hq)
      (by simp [ModInPlaceLayout.wires,List.mem_of_mem_take hz])
  have hdisA : (skywalkSharedUnused w).Disjoint
      ((skywalkSharedField w).a.take (skywalkSharedField w).low.length) := by
    apply List.disjoint_left.mpr
    intro q hq ha
    exact (skywalkShared_unused_outside w hn q hq)
      (by simp [ModInPlaceLayout.wires,List.mem_of_mem_take ha])
  have hu2 : regValue (skywalkSharedUnused w)
      (run (swapRegisters swap ((skywalkSharedField w).z.take (skywalkSharedField w).low.length) ((skywalkSharedField w).a.take (skywalkSharedField w).low.length))
        (m.drop (measurementCount (fusedSharedRetainedSignedHalf w g))) first).basis=0 := by
    exact (swap_preserves_disjoint_reg swap _ _ (skywalkSharedUnused w) hlen
      hsu hdisZ hdisA first
      (m.drop (measurementCount (fusedSharedRetainedSignedHalf w g)))).trans hu1
  refine ⟨h2.1.trans h1.1,?_,hu2⟩
  cases S <;> simpa [skywalkFieldNat,A] using h2.2

def FusedSharedReplayFrame (active swap g : Wire) (w : Nat → Wire)
    (base : BasisState) (C S G : Bool) (X Y : Nat) (st : BasisState) : Prop :=
  FusedSharedReplayValues active swap g w C S G X Y st ∧
  PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X Y st

theorem fusedSharedRetainedCell_frame (active swap g : Wire) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (hg : g∉fusedSharedIds.map w)
    (hnd : (active::swap::g::(skywalkSharedField w).wires).Nodup)
    (hgu : g∉skywalkSharedUnused w) (hsu : swap∉skywalkSharedUnused w)
    (base : BasisState) (X Y : Nat) (hX : X<p) (hY : Y<p) (C S G : Bool) :
    Triple (FusedSharedReplayFrame active swap g w base C S G X Y)
      (fusedSharedRetainedCell w g swap)
      (FusedSharedReplayFrame active swap g w base C S G
        (skywalkFieldNat p G S X Y).1 (skywalkFieldNat p G S X Y).2) := by
  intro s m h
  have hc := fusedSharedRetainedCell_spec active swap g w hn hg hnd hgu hsu
    X Y hX hY C S G s m h.1
  generalize hfirst : run (fusedSharedRetainedSignedHalf w g)
    (m.take (measurementCount (fusedSharedRetainedSignedHalf w g))) s=first
  have hgf := ReplayValues.control_nodup active swap g (skywalkSharedField w) hnd g (by simp)
  have hsigned := fusedSharedRetainedSignedHalf_correct w g hn hg hgf hgu X Y hX hY
    s (m.take (measurementCount (fusedSharedRetainedSignedHalf w g)))
    h.1.1.2.2.2.2.1 h.1.1.2.2.2.1 h.1.1.2.2.2.2.2 h.1.2
  rw [hfirst] at hsigned
  have hlen : ((skywalkSharedField w).z.take (skywalkSharedField w).low.length).length=
      ((skywalkSharedField w).a.take (skywalkSharedField w).low.length).length := by
    have hw := skywalkShared_field_widths w
    simp [List.length_take,ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hfull : (swap::(skywalkSharedField w).z++(skywalkSharedField w).a).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hd := List.nodup_iff_count.mp hnd q
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hd ⊢
    omega
  have htake : (swap::(skywalkSharedField w).z.take (skywalkSharedField w).low.length++
      (skywalkSharedField w).a.take (skywalkSharedField w).low.length).Nodup := by
    have hsub : (swap::(skywalkSharedField w).z.take (skywalkSharedField w).low.length++
        (skywalkSharedField w).a.take (skywalkSharedField w).low.length).Sublist
        (swap::(skywalkSharedField w).z++(skywalkSharedField w).a) :=
      ((List.take_sublist _ _).append (List.take_sublist _ _)).cons₂ swap
    exact hsub.nodup hfull
  have hswap := swapRegisters_correct swap
    ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
    ((skywalkSharedField w).a.take (skywalkSharedField w).low.length)
    hlen htake first (m.drop (measurementCount (fusedSharedRetainedSignedHalf w g)))
  have hrun : run (fusedSharedRetainedCell w g swap) m s=
      run (swapRegisters swap
        ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
        ((skywalkSharedField w).a.take (skywalkSharedField w).low.length))
        (m.drop (measurementCount (fusedSharedRetainedSignedHalf w g))) first := by
    rw [fusedSharedRetainedCell,run_append,hfirst]
  refine ⟨hc.1,hc.2,?_,?_,?_⟩
  · exact hc.2.1.2.2.2.1
  · exact hc.2.1.2.2.2.2.1
  · intro q hz ha
    rw [hrun]
    exact (hswap.2.1 q
      (fun hq => hz (List.mem_of_mem_take hq))
      (fun hq => ha (List.mem_of_mem_take hq))).trans
      ((hsigned.2.1 q hz).trans (h.2.2.2 q hz ha))

theorem fusedSharedRetainedCell_counts (w : Nat → Wire) (g swap : Wire)
    (hnd : (swap::(skywalkSharedField w).z++(skywalkSharedField w).a).Nodup) :
    toffoliCount (fusedSharedRetainedCell w g swap)=1794 ∧
    measurementCount (fusedSharedRetainedCell w g swap)=1538 := by
  have hw := skywalkShared_field_widths w
  have hz : (skywalkSharedField w).z.length=257 := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low]
  have hl : ((skywalkSharedField w).z.take (skywalkSharedField w).low.length).length=256 := by simp [hw.core.low,hz]
  have ha : ((skywalkSharedField w).a.take (skywalkSharedField w).low.length).length=256 := by simp [hw.core.low,hw.core.a]
  have htake : (swap::(skywalkSharedField w).z.take (skywalkSharedField w).low.length++(skywalkSharedField w).a.take (skywalkSharedField w).low.length).Nodup := by
    have hsub : (swap::(skywalkSharedField w).z.take (skywalkSharedField w).low.length++
        (skywalkSharedField w).a.take (skywalkSharedField w).low.length).Sublist
        (swap::(skywalkSharedField w).z++(skywalkSharedField w).a) :=
      ((List.take_sublist _ _).append (List.take_sublist _ _)).cons₂ swap
    exact hsub.nodup hnd
  have hs := swapRegisters_resources swap ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
    ((skywalkSharedField w).a.take (skywalkSharedField w).low.length) (hl.trans ha.symm)
    htake
  have hc := fusedSharedRetainedSignedHalf_counts w g
  simp only [fusedSharedRetainedCell,toffoliCount_append,measurementCount_append]
  rw [hc.1,hc.2,hs.1,hs.2.1,hl]
  norm_num

end ECDSAAdd.Arithmetic
