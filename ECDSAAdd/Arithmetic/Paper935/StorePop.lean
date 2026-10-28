import ECDSAAdd.Arithmetic.Paper935.StorePush

namespace ECDSAAdd.Arithmetic.Paper935

private theorem state_eq {a b : State} (h : a.phase=b.phase) (hb : a.basis=b.basis) : a=b := by
  cases a; cases b; simp_all

/-- Compute the store predicate, execute the actual reverse brigade, then
recompute the unchanged predicate to release the store control. -/
def storePop (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire) : Program :=
  storeFlag one zz pos sign output zb frozen positive low ++
    (popHistory output port record ++ storeFlag one zz pos sign output zb frozen positive low)

theorem storePop_run (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire)
    (hnz : (output::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::output::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
    (hworkpos : ∀ b∈frozen::positive::low,b.work≠pos)
    (s : State) (m : List Bool) (hone : s.basis one=true)
    (hzz : s.basis zz=false) (hpzero : s.basis pos=false)
    (hzw : ∀ b∈zb,s.basis b.work=false)
    (hfw : ∀ b∈frozen::positive::low,s.basis b.work=false)
    (hpush : (output::port::record).Nodup) (houtzero : s.basis output=false)
    (hout : output∉[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires)
    (hstable : List.Disjoint (port::record)
      ([one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires)) :
    let selected := !s.basis frozen.input &&
      !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
      decide (regValue (low.map ZeroBit.input) s.basis=0)
    let u : State := ⟨s.phase,writeBit s.basis output selected⟩
    let v := run (popHistory output port record)
      (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low))) u
    run (storePop one zz pos sign output port zb frozen positive low record) m s=
      ⟨s.phase,writeBit v.basis output false⟩ := by
  let selected := !s.basis frozen.input &&
    !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
    decide (regValue (low.map ZeroBit.input) s.basis=0)
  let u : State := ⟨s.phase,writeBit s.basis output selected⟩
  let v := run (popHistory output port record)
    (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low))) u
  have hfirst (tape : List Bool) : run (storeFlag one zz pos sign output zb frozen positive low) tape s=u := by
    rw [storeFlag_run one zz pos sign output zb frozen positive low hnz hnf hsg hpos hfr hlow hworkpos s tape hone hzz hpzero hzw hfw]
    simp [u,selected,houtzero]
  have hh := shift_frame output (port::record) u
    (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low)))
  have frame := And.intro hh.1 hh.2.1
  have inZ (w : Wire) (hw : w∈zb.flatMap ZeroBit.wires) :
      w∈[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires :=
    List.mem_append_left _ (List.mem_append_right _ hw)
  have inF (w : Wire) (hw : w∈(frozen::positive::low).flatMap ZeroBit.wires) :
      w∈[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires :=
    List.mem_append_right _ hw
  have root (w : Wire) (hw : w∈[one,zz,pos,sign]) :
      w∈[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires :=
    List.mem_append_left _ (List.mem_append_left _ hw)
  have keep (w : Wire)
      (hw : w∈[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires) :
      v.basis w=s.basis w := by
    have hp := List.disjoint_right.mp hstable hw
    have he : w≠output := fun hh => hout (hh ▸ hw)
    exact (frame.2 w hp).trans (Function.update_of_ne he _ _)
  have vout : v.basis output=selected := by
    exact (frame.2 output (List.nodup_cons.mp hpush).1).trans (by simp [u,writeBit])
  have vzwork : ∀ b∈zb,v.basis b.work=false := by
    intro b hb
    exact (keep b.work (inZ _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (hzw b hb)
  have vfwork : ∀ b∈frozen::positive::low,v.basis b.work=false := by
    intro b hb
    exact (keep b.work (inF _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (hfw b hb)
  have vzreg : regValue (zb.map ZeroBit.input) v.basis=regValue (zb.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    exact keep _ (inZ _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))
  have vlreg : regValue (low.map ZeroBit.input) v.basis=regValue (low.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    exact keep _ (inF _ (List.mem_flatMap.mpr ⟨b,by simp [hb],by simp [ZeroBit.wires]⟩))
  have vfr : v.basis frozen.input=s.basis frozen.input :=
    keep _ (inF _ (List.mem_flatMap.mpr ⟨frozen,by simp,by simp [ZeroBit.wires]⟩))
  have hlast (tape : List Bool) : run (storeFlag one zz pos sign output zb frozen positive low) tape v=
      ⟨s.phase,writeBit v.basis output false⟩ := by
    rw [storeFlag_run one zz pos sign output zb frozen positive low hnz hnf hsg hpos hfr hlow hworkpos v tape
      ((keep one (root _ (by simp))).trans hone) ((keep zz (root _ (by simp))).trans hzz)
      ((keep pos (root _ (by simp))).trans hpzero) vzwork vfwork]
    rw [vzreg,vlreg,vfr,keep sign (root _ (by simp)),vout]
    simp only [selected,Bool.xor_self]
    exact congrArg (fun ph => State.mk ph (writeBit v.basis output false)) frame.1
  dsimp only
  rw [storePop,run_append,run_take,hfirst,run_append,run_take,hlast]

theorem storeHistory_roundtrip (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire)
    (hnz : (output::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::output::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
    (hworkpos : ∀ b∈frozen::positive::low,b.work≠pos)
    (s : State) (m : List Bool) (hone : s.basis one=true)
    (hzz : s.basis zz=false) (hpzero : s.basis pos=false)
    (hzw : ∀ b∈zb,s.basis b.work=false)
    (hfw : ∀ b∈frozen::positive::low,s.basis b.work=false)
    (hpush : (output::port::record).Nodup) (houtzero : s.basis output=false)
    (hout : output∉[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires)
    (hstable : List.Disjoint (port::record)
      ([one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires))
    (hfit : (!s.basis frozen.input &&
      !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
      decide (regValue (low.map ZeroBit.input) s.basis=0))=true →
      2*regValue record s.basis+(s.basis port).toNat<2^record.length) (n : List Bool) :
    run (storePop one zz pos sign output port zb frozen positive low record) n
      (run (storePush one zz pos sign output port zb frozen positive low record) m s)=s := by
  let selected := !s.basis frozen.input &&
    !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
    decide (regValue (low.map ZeroBit.input) s.basis=0)
  let u : State := ⟨s.phase,writeBit s.basis output selected⟩
  let v := run (pushHistory output port record)
    (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low))) u
  let t := run (storePush one zz pos sign output port zb frozen positive low record) m s
  have he := storePush_run one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr hlow hworkpos s m hone hzz hpzero hzw hfw hpush houtzero hout hstable
  have hs := storePush_spec one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr hlow hworkpos s m hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit
  let data := [one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires
  have keep (w : Wire) (hw : w∈data) : t.basis w=s.basis w :=
    hs.2.2.2.2 w (List.disjoint_right.mp hstable hw)
  have root (w : Wire) (hw : w∈[one,zz,pos,sign]) : w∈data :=
    List.mem_append_left _ (List.mem_append_left _ hw)
  have inZ (w : Wire) (hw : w∈zb.flatMap ZeroBit.wires) : w∈data :=
    List.mem_append_left _ (List.mem_append_right _ hw)
  have inF (w : Wire) (hw : w∈(frozen::positive::low).flatMap ZeroBit.wires) : w∈data :=
    List.mem_append_right _ hw
  have tzw : ∀ b∈zb,t.basis b.work=false := by
    intro b hb
    exact (keep b.work (inZ _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (hzw b hb)
  have tfw : ∀ b∈frozen::positive::low,t.basis b.work=false := by
    intro b hb
    exact (keep b.work (inF _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (hfw b hb)
  have tzreg : regValue (zb.map ZeroBit.input) t.basis=regValue (zb.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    exact keep _ (inZ _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))
  have tlreg : regValue (low.map ZeroBit.input) t.basis=regValue (low.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    exact keep _ (inF _ (List.mem_flatMap.mpr ⟨b,by simp [hb],by simp [ZeroBit.wires]⟩))
  have tfr : t.basis frozen.input=s.basis frozen.input :=
    keep _ (inF _ (List.mem_flatMap.mpr ⟨frozen,by simp,by simp [ZeroBit.wires]⟩))
  have hpop := storePop_run one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr hlow hworkpos t n
    ((keep one (root _ (by simp))).trans hone) ((keep zz (root _ (by simp))).trans hzz)
    ((keep pos (root _ (by simp))).trans hpzero) tzw tfw hpush hs.2.1 hout hstable
  dsimp only at hpop
  rw [tfr,tzreg,tlreg,keep sign (root _ (by simp))] at hpop
  have vf := (shift_frame output (port::record) u
    (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low)))).2.2
  have vo : v.basis output=selected :=
    (vf.2 output (List.nodup_cons.mp hpush).1).trans (by simp [u,writeBit])
  have restored : (⟨t.phase,writeBit t.basis output selected⟩ : State)=v := by
    change t=⟨s.phase,writeBit v.basis output false⟩ at he
    rw [he]
    apply state_eq
    · exact vf.1.symm
    · funext w
      by_cases hw : w=output
      · subst w; simp [writeBit,vo]
      · simp [writeBit,hw]
  rw [restored] at hpop
  have sameTape : run (popHistory output port record)
      (n.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low))) v =
      run (popHistory output port record)
      (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low))) v := by
    calc
      _ = run (popHistory output port record) [] v := by
        rw [←run_take, (history_counts output port record).2.2.2,List.take_zero]
      _ = _ := by
        symm
        rw [←run_take, (history_counts output port record).2.2.2,List.take_zero]
  rw [sameTape,history_roundtrip output port record hpush u] at hpop
  change run (storePop one zz pos sign output port zb frozen positive low record) n t=s
  rw [hpop,hs.1]
  apply state_eq
  · rfl
  · funext w
    by_cases hw : w=output
    · subst w; simp [writeBit,houtzero]
    · simp [u,writeBit,hw]

theorem storePushForget_pop_stored (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire)
    (hnz : (output::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::output::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
    (hworkpos : ∀ b∈frozen::positive::low,b.work≠pos)
    (s : State) (m : List Bool) (hone : s.basis one=true)
    (hzz : s.basis zz=false) (hpzero : s.basis pos=false)
    (hzw : ∀ b∈zb,s.basis b.work=false)
    (hfw : ∀ b∈frozen::positive::low,s.basis b.work=false)
    (hpush : (output::port::record).Nodup) (houtzero : s.basis output=false)
    (hout : output∉[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires)
    (hstable : List.Disjoint (port::record)
      ([one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires))
    (hfit : (!s.basis frozen.input &&
      !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
      decide (regValue (low.map ZeroBit.input) s.basis=0))=true →
      2*regValue record s.basis+(s.basis port).toNat<2^record.length) (n : List Bool) (ordinal : Nat)
    (hselected : (!s.basis frozen.input &&
      !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
      decide (regValue (low.map ZeroBit.input) s.basis=0))=true) :
    run (storePop one zz pos sign output port zb frozen positive low record) n
      (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)=s := by
  have hs := storePush_spec one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr hlow hworkpos s (m.drop ordinal) hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit
  have hf := storePushForget_run one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr hlow hworkpos s m hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit ordinal
  let t := run (storePush one zz pos sign output port zb frozen positive low record) (m.drop ordinal) s
  have hport : t.basis port=false := by simpa only [hselected,ite_true] using hs.2.2.1
  have same : runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s=t := by
    rw [hf]
    simp only [hselected,Bool.not_true,Bool.false_and,Bool.and_false,Bool.xor_false]
    apply state_eq
    · exact hs.1.symm
    · funext w
      by_cases hw : w=port
      · subst w; simp [writeBit,hport]
      · exact Function.update_of_ne hw _ _
  rw [same]
  exact storeHistory_roundtrip one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr hlow hworkpos s (m.drop ordinal) hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit n

theorem storePop_counts (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire) :
    toffoliCount (storePop one zz pos sign output port zb frozen positive low record)=
      8*zb.length+2*low.length+8+record.length ∧
    measurementCount (storePop one zz pos sign output port zb frozen positive low record)=
      8*zb.length+2*low.length+4 := by
  have hf := storeFlag_counts one zz pos sign output zb frozen positive low
  have hh := history_counts output port record
  simp only [storePop,toffoliCount_append,measurementCount_append,hf.1,hf.2,hh.2.2.1,hh.2.2.2]
  constructor <;> omega

theorem storePop_support (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire) :
    wires (storePop one zz pos sign output port zb frozen positive low record)=
      wires (storeFlag one zz pos sign output zb frozen positive low) ∪ wires (popHistory output port record) := by
  rw [storePop,wires_append,wires_append]
  ext w
  simp only [Finset.mem_union]
  tauto


end ECDSAAdd.Arithmetic.Paper935
