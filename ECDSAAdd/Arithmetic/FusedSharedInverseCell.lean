import ECDSAAdd.Arithmetic.FusedFieldInverseBridge
import ECDSAAdd.Arithmetic.FusedSharedRetainedReplay

namespace ECDSAAdd.Arithmetic
open Secp256k1

def fusedSharedInverseSigned (w : Nat → Wire) (g : Wire) : Program :=
  fusedFieldSignedHalf g (fusedSharedPorts w g).compactInverseProgram

theorem fusedSharedInverseSigned_counts (w : Nat → Wire) (g : Wire) :
    toffoliCount (fusedSharedInverseSigned w g)=1538 ∧
    measurementCount (fusedSharedInverseSigned w g)=1538 :=
  fusedFieldSignedHalf_counts g (fusedSharedPorts w g).compactInverseProgram 1538 1538
    (compactShared_inverse_counts w g)

theorem fusedSharedInverseSigned_correct (w : Nat → Wire) (g : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hg : g∉fusedSharedIds.map w)
    (hgf : (g::(skywalkSharedField w).wires).Nodup)
    (hgu : g∉skywalkSharedUnused w)
    (X Y : Nat) (hX : X<p) (hY : Y<p) (s : State) (record : List Bool)
    (hy : regValue (skywalkSharedField w).a s.basis=Y)
    (hx : regValue (skywalkSharedField w).z s.basis=X)
    (hk : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0) :
    (run (fusedSharedInverseSigned w g) record s).phase=s.phase ∧
    (∀ q,q∉(skywalkSharedField w).z →
      (run (fusedSharedInverseSigned w g) record s).basis q=s.basis q) ∧
    regValue (skywalkSharedField w).z
      (run (fusedSharedInverseSigned w g) record s).basis=
      (skywalkFieldUnnat p (s.basis g) false X Y).1 := by
  have hkernel : ∀ st : State, ∀ ms : List Bool,
      regValue (skywalkSharedField w).a st.basis=Y →
      regValue (skywalkSharedField w).z st.basis=X →
      regValue (skywalkSharedField w).work st.basis=0 →
      regValue (skywalkSharedUnused w) st.basis=0 →
      (run (fusedSharedPorts w g).compactInverseProgram ms st).phase=st.phase ∧
      (∀ q,q∉(skywalkSharedField w).z →
        (run (fusedSharedPorts w g).compactInverseProgram ms st).basis q=st.basis q) ∧
      regValue (skywalkSharedField w).z
        (run (fusedSharedPorts w g).compactInverseProgram ms st).basis=
        FusedSignedHalf.inverseValue (st.basis g) X Y := by
    intro st ms hy' hx' hk' hu'
    exact fusedSharedInverseKernel_correct w g hn hg X Y hX hY st ms hy' hx' hk' hu'
  unfold fusedSharedInverseSigned
  exact fusedFieldInverse_correct (skywalkSharedField w) (skywalkSharedUnused w)
    g (fusedSharedPorts w g).compactInverseProgram X Y hX hY hgf hgu hkernel
    s record hy hx hk hu


/-- Swap undo precedes the independently measured inverse arithmetic. -/
def fusedSharedInverseCell (w : Nat → Wire) (g swap : Wire) : Program :=
  swapRegisters swap ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
    ((skywalkSharedField w).a.take (skywalkSharedField w).low.length) ++
    fusedSharedInverseSigned w g

private theorem inverse_unused_clean (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (base s : BasisState) (X Y : Nat) (hu : regValue (skywalkSharedUnused w) base=0)
    (h : PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X Y s) :
    regValue (skywalkSharedUnused w) s=0 := by
  apply Eq.trans (regValue_congr _ _ _ ?_) hu
  intro q hq
  have ho := skywalkShared_unused_outside w hn q hq
  exact h.2.2 q
    (fun hz => ho (by simp [ModInPlaceLayout.wires,hz]))
    (fun ha => ho (by simp [ModInPlaceLayout.wires,ha]))

private theorem inverse_swap_frame (active swap g : Wire) (w : Nat → Wire)
    (hnd : (active::swap::g::(skywalkSharedField w).wires).Nodup)
    (base : BasisState) (hk : regValue (skywalkSharedField w).work base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (swapRegisters swap ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
        ((skywalkSharedField w).a.take (skywalkSharedField w).low.length))
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (if base swap then Y.val else X.val) (if base swap then X.val else Y.val)) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hw := skywalkShared_field_widths w
  have hlen : ((skywalkSharedField w).z.take (skywalkSharedField w).low.length).length=
      ((skywalkSharedField w).a.take (skywalkSharedField w).low.length).length := by
    simp [List.length_take,ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hfull : (swap::(skywalkSharedField w).z++(skywalkSharedField w).a).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp hnd q
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hc ⊢
    omega
  have htake : (swap::(skywalkSharedField w).z.take (skywalkSharedField w).low.length++
      (skywalkSharedField w).a.take (skywalkSharedField w).low.length).Nodup :=
    (((List.take_sublist _ _).append (List.take_sublist _ _)).cons₂ swap).nodup hfull
  intro s m h
  have control (q : Wire) (hq : q∈[active,swap,g]) : s.basis q=base q :=
    h.2.2 q (ReplayValues.control_outside active swap g (skywalkSharedField w) hnd q hq).1
      (ReplayValues.control_outside active swap g (skywalkSharedField w) hnd q hq).2
  have pre : ReplayValues active swap g (skywalkSharedField w)
      (base active) (base swap) (base g) X.val Y.val s.basis :=
    ⟨control active (by simp),control swap (by simp),control g (by simp),h.1,h.2.1,
      fusedShared_work_clean active g swap w hnd base s.basis X.val Y.val hk h⟩
  obtain ⟨hf,hout⟩ := ReplayValues.swap_step active swap g (skywalkSharedField w) 256
    X.val Y.val (base active) (base swap) (base g) hw hnd
    ((ZMod.val_lt X).trans (by norm_num [p])) ((ZMod.val_lt Y).trans (by norm_num [p])) s m pre
  have hs := swapRegisters_correct swap
    ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
    ((skywalkSharedField w).a.take (skywalkSharedField w).low.length) hlen htake s m
  exact ⟨hf,hout.2.2.2.1,hout.2.2.2.2.1,fun q hz ha =>
    (hs.2.1 q (fun hm => hz (List.mem_of_mem_take hm))
      (fun hm => ha (List.mem_of_mem_take hm))).trans (h.2.2 q hz ha)⟩

private theorem inverse_signed_frame (active swap g : Wire) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (hg : g∉fusedSharedIds.map w)
    (hnd : (active::swap::g::(skywalkSharedField w).wires).Nodup)
    (hgu : g∉skywalkSharedUnused w)
    (base : BasisState) (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (fusedSharedInverseSigned w g)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (2*X+(if base g then -Y else Y)).val Y.val) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hgf := ReplayValues.control_nodup active swap g (skywalkSharedField w) hnd g (by simp)
  have hdis : (skywalkSharedField w).z.Disjoint (skywalkSharedField w).a := by
    apply List.disjoint_left.mpr
    intro q hz ha
    have hc := List.nodup_iff_count.mp hnd q
    have hZ := List.count_pos_iff.mpr hz
    have hA := List.count_pos_iff.mpr ha
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hc
    omega
  intro s m h
  have gval : s.basis g=base g := h.2.2 g
    (ReplayValues.control_outside active swap g (skywalkSharedField w) hnd g (by simp)).1
    (ReplayValues.control_outside active swap g (skywalkSharedField w) hnd g (by simp)).2
  have hwork := fusedShared_work_clean active g swap w hnd base s.basis X.val Y.val hk h
  have hunused := inverse_unused_clean w hn base s.basis X.val Y.val hu h
  obtain ⟨hf,he,hv⟩ := fusedSharedInverseSigned_correct w g hn hg hgf hgu X.val Y.val
    (ZMod.val_lt X) (ZMod.val_lt Y) s m h.2.1 h.1 hwork hunused
  have hb : (skywalkFieldUnnat p (base g) false X.val Y.val).1<p := by
    cases base g <;> simp only [skywalkFieldUnnat,skywalkSignedNat,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true]
    all_goals exact Nat.mod_lt _ p_prime.pos
  have fld := skywalkFieldUnnat_field (base g) false X.val Y.val (ZMod.val_lt X) (ZMod.val_lt Y)
  have v := congrArg (fun q : Fp×Fp => q.1.val) fld
  simp only at v
  rw [ZMod.val_natCast_of_lt hb] at v
  simp only [skywalkPayloadUncell,Bool.false_eq_true,if_false,ZMod.natCast_zmod_val] at v
  rw [gval] at hv
  exact ⟨hf,PairFrame.update_temp (skywalkSharedField w).z (skywalkSharedField w).a
    base s.basis _ X.val Y.val _ hdis h he (hv.trans v)⟩

theorem fusedSharedInverse_leaf_frame (active swap g : Wire) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (hg : g∉fusedSharedIds.map w)
    (hnd : (active::swap::g::(skywalkSharedField w).wires).Nodup)
    (hgu : g∉skywalkSharedUnused w)
    (base : BasisState) (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (fusedSharedInverseCell w g swap)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (skywalkPayloadUncell (base g) (base swap) (X,Y)).1.val
        (skywalkPayloadUncell (base g) (base swap) (X,Y)).2.val) := by
  let A := if base swap then Y else X
  let B := if base swap then X else Y
  have h1 := inverse_swap_frame active swap g w hnd base hk X Y
  have h2 := inverse_signed_frame active swap g w hn hg hnd hgu base hk hu A B
  have hpair : PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
      (if base swap then Y.val else X.val) (if base swap then X.val else Y.val)=
      PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base A.val B.val := by
    cases hs : base swap <;> simp [A,B,hs]
  rw [hpair] at h1
  cases hs : base swap <;>
    simpa only [fusedSharedInverseCell,skywalkPayloadUncell,A,B,hs,
      Bool.false_eq_true,if_false,if_true] using h1.seq h2

theorem fusedSharedInverseCell_counts (w : Nat → Wire) (g swap : Wire)
    (hnd : (swap::(skywalkSharedField w).z++(skywalkSharedField w).a).Nodup) :
    toffoliCount (fusedSharedInverseCell w g swap)=1794 ∧
    measurementCount (fusedSharedInverseCell w g swap)=1538 := by
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
  have hc := fusedSharedInverseSigned_counts w g
  simp only [fusedSharedInverseCell,toffoliCount_append,measurementCount_append]
  rw [hc.1,hc.2,hs.1,hs.2.1,hl]
  norm_num

end ECDSAAdd.Arithmetic
