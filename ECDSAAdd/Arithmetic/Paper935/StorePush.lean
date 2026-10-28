import ECDSAAdd.Arithmetic.Paper935.StoreFlag
import ECDSAAdd.Arithmetic.Paper935.History

namespace ECDSAAdd.Arithmetic.Paper935

/-- Compute the store predicate, execute the actual finite brigade, then
recompute the unchanged predicate to release the store control. -/
def storePush (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire) : Program :=
  storeFlag one zz pos sign output zb frozen positive low ++
    (pushHistory output port record ++ storeFlag one zz pos sign output zb frozen positive low)

theorem storePush_run (one zz pos sign output port : Wire) (zb : List ZeroBit)
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
    let v := run (pushHistory output port record)
      (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low))) u
    run (storePush one zz pos sign output port zb frozen positive low record) m s=
      ⟨s.phase,writeBit v.basis output false⟩ := by
  let selected := !s.basis frozen.input &&
    !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
    decide (regValue (low.map ZeroBit.input) s.basis=0)
  let u : State := ⟨s.phase,writeBit s.basis output selected⟩
  let v := run (pushHistory output port record)
    (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low))) u
  have hfirst (tape : List Bool) : run (storeFlag one zz pos sign output zb frozen positive low) tape s=u := by
    rw [storeFlag_run one zz pos sign output zb frozen positive low hnz hnf hsg hpos hfr hlow hworkpos s tape hone hzz hpzero hzw hfw]
    simp [u,selected,houtzero]
  have frame := (shift_frame output (port::record) u
    (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low)))).2.2
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
  rw [storePush,run_append,run_take,hfirst,run_append,run_take,hlast]

theorem storePush_spec (one zz pos sign output port : Wire) (zb : List ZeroBit)
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
      2*regValue record s.basis+(s.basis port).toNat<2^record.length) :
    let selected := !s.basis frozen.input &&
      !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
      decide (regValue (low.map ZeroBit.input) s.basis=0)
    let t := run (storePush one zz pos sign output port zb frozen positive low record) m s
    t.phase=s.phase ∧ t.basis output=false ∧
      t.basis port=(if selected then false else s.basis port) ∧
      regValue record t.basis=(if selected then
        2*regValue record s.basis+(s.basis port).toNat else regValue record s.basis) ∧
      ∀ w,w∉port::record → t.basis w=s.basis w := by
  let selected := !s.basis frozen.input &&
      !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
      decide (regValue (low.map ZeroBit.input) s.basis=0)
  let u : State := ⟨s.phase,writeBit s.basis output selected⟩
  let v := run (pushHistory output port record)
    (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low))) u
  have he := storePush_run one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr hlow hworkpos s m hone hzz hpzero hzw hfw hpush houtzero hout hstable
  have hn := (List.nodup_cons.mp hpush).1
  have hop : port≠output := fun hh => hn (by simp [hh])
  have uport : u.basis port=s.basis port := Function.update_of_ne hop _ _
  have ureg : regValue record u.basis=regValue record s.basis := by
    apply regValue_congr
    intro w hw
    exact Function.update_of_ne (fun (hh : w=output) => hn (List.mem_cons_of_mem _ (hh ▸ hw))) _ _
  have hp := pushHistory_spec output port record hpush u
    (m.drop (measurementCount (storeFlag one zz pos sign output zb frozen positive low))) (by
      intro hs
      have hsel : selected=true := by simpa [u,writeBit] using hs
      rw [ureg,uport]
      exact hfit hsel)
  have hfinalreg : regValue record (writeBit v.basis output false)=regValue record v.basis := by
    apply regValue_congr
    intro w hw
    exact Function.update_of_ne (fun (hh : w=output) => hn (List.mem_cons_of_mem _ (hh ▸ hw))) _ _
  dsimp only
  rw [he]
  refine ⟨rfl,by simp [writeBit],?_,?_,?_⟩
  · change writeBit v.basis output false port=(if selected then false else s.basis port)
    rw [show writeBit v.basis output false port=v.basis port from Function.update_of_ne hop _ _,hp.2.2.1,uport]
    simp [u,writeBit,selected]
  · change regValue record (writeBit v.basis output false)=(if selected then 2*regValue record s.basis+(s.basis port).toNat else regValue record s.basis)
    rw [hfinalreg,hp.2.2.2.1,ureg,uport]
    simp [u,writeBit,selected]
  · intro w hw
    by_cases ho : w=output
    · subst w; simp [writeBit,houtzero]
    · exact (Function.update_of_ne ho _ _).trans ((hp.2.2.2.2 w hw).trans (Function.update_of_ne ho _ _))

def storePushForget (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire) : RecordedProgram :=
  embedRecorded (storePush one zz pos sign output port zb frozen positive low record) ++
    ECDSAAdd.Arithmetic.Divsteps.forgetBranch port

theorem storePushForget_run (one zz pos sign output port : Wire) (zb : List ZeroBit)
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
      2*regValue record s.basis+(s.basis port).toNat<2^record.length) (ordinal : Nat) :
    let selected := !s.basis frozen.input &&
      !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
      decide (regValue (low.map ZeroBit.input) s.basis=0)
    let segment := storePush one zz pos sign output port zb frozen positive low record
    let t := run segment (m.drop ordinal) s
    runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s=
      ⟨s.phase ^^ (m.getD (ordinal+measurementCount segment) false && (!selected && s.basis port)),
        writeBit t.basis port false⟩ := by
  have hs := storePush_spec one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr hlow hworkpos s (m.drop ordinal) hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit
  dsimp only
  rw [storePushForget,runWithTape_append,runWithTape_embedRecorded,(embedRecorded_counts _).2,
    ECDSAAdd.Arithmetic.Divsteps.forgetBranch_run,hs.1,hs.2.2.1]
  cases (!s.basis frozen.input &&
      !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
      decide (regValue (low.map ZeroBit.input) s.basis=0)) <;> simp

theorem storePush_counts (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire) :
    toffoliCount (storePush one zz pos sign output port zb frozen positive low record)=
      8*zb.length+2*low.length+8+record.length ∧
    measurementCount (storePush one zz pos sign output port zb frozen positive low record)=
      8*zb.length+2*low.length+4 := by
  have hf := storeFlag_counts one zz pos sign output zb frozen positive low
  have hh := history_counts output port record
  simp only [storePush,toffoliCount_append,measurementCount_append,hf.1,hf.2,hh.1,hh.2.1]
  constructor <;> omega

theorem storePush_support (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire) :
    wires (storePush one zz pos sign output port zb frozen positive low record)=
      wires (storeFlag one zz pos sign output zb frozen positive low) ∪ wires (pushHistory output port record) := by
  rw [storePush,wires_append,wires_append]
  ext w
  simp only [Finset.mem_union]
  tauto

theorem storePushForget_counts (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire) :
    recordedToffoliCount (storePushForget one zz pos sign output port zb frozen positive low record)=
      8*zb.length+2*low.length+8+record.length ∧
    recordedMeasurementCount (storePushForget one zz pos sign output port zb frozen positive low record)=
      8*zb.length+2*low.length+5 := by
  have hp := storePush_counts one zz pos sign output port zb frozen positive low record
  have hf := ECDSAAdd.Arithmetic.Divsteps.forgetBranch_resources port
  simp only [storePushForget,recordedToffoliCount_append,recordedMeasurementCount_append,
    (embedRecorded_counts _).1,(embedRecorded_counts _).2,hp.1,hp.2,hf.1,hf.2.1,Nat.add_zero]
  exact ⟨trivial,trivial⟩

theorem storePushForget_wellFormed (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire) (cursor : Nat) :
    RecordedWellFormedAt cursor (storePushForget one zz pos sign output port zb frozen positive low record) := by
  rw [storePushForget,RecordedWellFormedAt_append]
  exact ⟨embedRecorded_wellFormed _ _,by simp [ECDSAAdd.Arithmetic.Divsteps.forgetBranch,RecordedWellFormedAt]⟩

theorem storePushForget_support (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire) :
    recordedWires (storePushForget one zz pos sign output port zb frozen positive low record)=
      wires (storePush one zz pos sign output port zb frozen positive low record) ∪ {port} := by
  rw [storePushForget,recordedWires_append,embedRecorded_wires,
    (ECDSAAdd.Arithmetic.Divsteps.forgetBranch_resources port).2.2]

end ECDSAAdd.Arithmetic.Paper935
