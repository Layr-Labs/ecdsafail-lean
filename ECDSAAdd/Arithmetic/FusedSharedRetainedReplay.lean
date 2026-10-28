import ECDSAAdd.Arithmetic.FusedSharedRetainedCell
import ECDSAAdd.Arithmetic.SkywalkDialog

namespace ECDSAAdd.Arithmetic
open Secp256k1

private theorem retained_cell_bound (q : Nat) (G S : Bool) (X Y : Nat)
    (hp0 : 0<q) (hp : q%2=1) (_hX : X<q) (hY : Y<q) :
    (skywalkFieldNat q G S X Y).1<q ∧ (skywalkFieldNat q G S X Y).2<q := by
  have hd : skywalkSignedNat q G X Y<q := by
    cases G
    · change (X+q-Y)%q<q
      exact Nat.mod_lt _ hp0
    · change (X+Y)%q<q
      exact Nat.mod_lt _ hp0
  have hh := halve_mod_bound q _ hp hd
  cases S <;> simp only [skywalkFieldNat,Bool.false_eq_true,if_false,if_true]
  · exact ⟨hh,hY⟩
  · exact ⟨hY,hh⟩

theorem fusedShared_work_clean (active g swap : Wire) (w : Nat → Wire)
    (hn : (active::swap::g::(skywalkSharedField w).wires).Nodup)
    (base s : BasisState) (X Y : Nat)
    (hk : regValue (skywalkSharedField w).work base=0)
    (h : PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X Y s) :
    regValue (skywalkSharedField w).work s=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  have hc := List.nodup_iff_count.mp hn q
  have hW := List.count_pos_iff.mpr hq
  have awayZ : q∉(skywalkSharedField w).z := by
    intro hz
    have hZ := List.count_pos_iff.mpr hz
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hc
    omega
  have awayA : q∉(skywalkSharedField w).a := by
    intro ha
    have hA := List.count_pos_iff.mpr ha
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hc
    omega
  rw [h.2.2 q awayZ awayA]
  exact (regValue_zero _ _).mp hk q hq

private theorem retained_unused_clean (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (base s : BasisState) (X Y : Nat) (hu : regValue (skywalkSharedUnused w) base=0)
    (h : PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X Y s) :
    regValue (skywalkSharedUnused w) s=0 := by
  apply Eq.trans (regValue_congr _ _ _ ?_) hu
  intro q hq
  have ho := skywalkShared_unused_outside w hn q hq
  exact h.2.2 q
    (fun hz => ho (by simp [ModInPlaceLayout.wires,hz]))
    (fun ha => ho (by simp [ModInPlaceLayout.wires,ha]))

theorem fusedSharedRetained_leaf_frame (active swap g : Wire) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (hg : g∉fusedSharedIds.map w)
    (hnd : (active::swap::g::(skywalkSharedField w).wires).Nodup)
    (hgu : g∉skywalkSharedUnused w) (hsu : swap∉skywalkSharedUnused w)
    (base : BasisState) (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (fusedSharedRetainedCell w g swap)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (skywalkPayloadCell (base g) (base swap) (X,Y)).1.val
        (skywalkPayloadCell (base g) (base swap) (X,Y)).2.val) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  intro s m h
  have control (q : Wire) (hq : q∈[active,swap,g]) : s.basis q=base q :=
    h.2.2 q (ReplayValues.control_outside active swap g (skywalkSharedField w) hnd q hq).1
      (ReplayValues.control_outside active swap g (skywalkSharedField w) hnd q hq).2
  have hwork := fusedShared_work_clean active g swap w hnd base s.basis X.val Y.val hk h
  have hunused := retained_unused_clean w hn base s.basis X.val Y.val hu h
  have pre : FusedSharedReplayFrame active swap g w base
      (base active) (base swap) (base g) X.val Y.val s.basis :=
    ⟨⟨⟨control active (by simp),control swap (by simp),control g (by simp),
      h.1,h.2.1,hwork⟩,hunused⟩,h⟩
  obtain ⟨hf,hout⟩ := fusedSharedRetainedCell_frame active swap g w hn hg hnd
    hgu hsu base X.val Y.val (ZMod.val_lt X) (ZMod.val_lt Y)
    (base active) (base swap) (base g) s m pre
  have hb := retained_cell_bound p (base g) (base swap) X.val Y.val
    p_prime.pos (by norm_num [p]) (ZMod.val_lt X) (ZMod.val_lt Y)
  have he := skywalkFieldNat_field (base g) (base swap) X.val Y.val (ZMod.val_lt Y)
  simp only [ZMod.natCast_zmod_val] at he
  have hx := congrArg (fun q : Fp×Fp => q.1.val) he
  have hy := congrArg (fun q : Fp×Fp => q.2.val) he
  simp only at hx hy
  rw [ZMod.val_natCast_of_lt hb.1] at hx
  rw [ZMod.val_natCast_of_lt hb.2] at hy
  exact ⟨hf,hout.2.1.trans hx,hout.2.2.1.trans hy,hout.2.2.2⟩

def FusedSharedTapeLayout (w : Nat → Wire) (rs : List (Wire×Wire)) : Prop :=
  ∀ r∈rs,r.1∉fusedSharedIds.map w ∧
    r.1∉skywalkSharedUnused w ∧ r.2∉skywalkSharedUnused w

theorem skywalkShared_fused_tape_layout (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    FusedSharedTapeLayout w (skywalkSharedTape w) := by
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  have hib : i<512 := List.mem_range.mp hi
  have away (j : Nat) (hj : j<2314)
      (hneq : j≠769 ∧ j≠1027 ∧ j≠2054 ∧ j≠2055) :
      w j∉skywalkSharedUnused w := by
    intro hm
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with he|he|he|he
    all_goals
      have hh := skywalkShared_index_inj w hn j _ hj (by omega) he
      omega
  exact ⟨(fusedSharedSites_record_outside w hn i hib).1,
    away i (by omega) (by omega),away (1028+i) (by omega) (by omega)⟩

def fusedSharedRetainedReplay (w : Nat → Wire) : List (Wire×Wire) → Program
  | [] => []
  | r::rs => fusedSharedRetainedCell w r.1 r.2 ++ fusedSharedRetainedReplay w rs

theorem fusedSharedRetainedReplay_spec (active : Wire) (w : Nat → Wire)
    (rs : List (Wire×Wire)) (hn : (skywalkSharedWires w).Nodup)
    (ht : SkywalkTapeLayout active (skywalkSharedField w) rs)
    (hf : FusedSharedTapeLayout w rs) (base : BasisState)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (fusedSharedRetainedReplay w rs)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (skywalkPayloadReplay (skywalkTapeControls base rs) (X,Y)).1.val
        (skywalkPayloadReplay (skywalkTapeControls base rs) (X,Y)).2.val) := by
  induction rs generalizing X Y with
  | nil => intro st m h; exact ⟨rfl,h⟩
  | cons r rs ih =>
    have hr := ht r (by simp)
    have ht' : SkywalkTapeLayout active (skywalkSharedField w) rs :=
      fun q hq => ht q (by simp [hq])
    have hf0 := hf r (by simp)
    have hf' : FusedSharedTapeLayout w rs := fun q hq => hf q (by simp [hq])
    let Q := skywalkPayloadCell (base r.1) (base r.2) (X,Y)
    have h1 := fusedSharedRetained_leaf_frame active r.2 r.1 w hn hf0.1 hr
      hf0.2.1 hf0.2.2 base hk hu X Y
    have h2 := ih ht' hf' Q.1 Q.2
    simpa only [fusedSharedRetainedReplay,skywalkTapeControls,List.map_cons,
      skywalkPayloadReplay,Q] using h1.seq h2

theorem fusedSharedRetainedReplay_counts (active : Wire) (w : Nat → Wire)
    (rs : List (Wire×Wire)) (ht : SkywalkTapeLayout active (skywalkSharedField w) rs) :
    toffoliCount (fusedSharedRetainedReplay w rs)=rs.length*1794 ∧
    measurementCount (fusedSharedRetainedReplay w rs)=rs.length*1538 := by
  induction rs with
  | nil => simp [fusedSharedRetainedReplay,toffoliCount,measurementCount]
  | cons r rs ih =>
    have hr := ht r (by simp)
    have ht' : SkywalkTapeLayout active (skywalkSharedField w) rs :=
      fun q hq => ht q (by simp [hq])
    have hnd : (r.2::(skywalkSharedField w).z++(skywalkSharedField w).a).Nodup := by
      apply List.nodup_iff_count.mpr
      intro q
      have hc := List.nodup_iff_count.mp hr q
      simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hc ⊢
      omega
    have hc := fusedSharedRetainedCell_counts w r.1 r.2 hnd
    have hi := ih ht'
    simp only [fusedSharedRetainedReplay,toffoliCount_append,measurementCount_append,
      hc.1,hc.2,hi.1,hi.2,List.length_cons,Nat.add_mul]
    omega

end ECDSAAdd.Arithmetic
