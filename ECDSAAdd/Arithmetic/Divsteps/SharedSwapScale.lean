import ECDSAAdd.Arithmetic.Divsteps.SharedSwapGap
import ECDSAAdd.Arithmetic.Divsteps.ScaleRemoval

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- One actual measured-swap step with modular scale removal before recovery.
The halving reads the actual active control computed by the forward step. -/
def StepLayout.swapScaleStep (L : StepLayout) (U : ModUnaryLayout) (p cursor : Nat) : RecordedProgram :=
  L.swapAround (embedRecorded (reverseHalf L.history.active U p)) cursor

/-- All step/history/work bits and input phase are restored while the separate
accumulator is halved exactly for active inputs. The original swap outcome is
used after the intervening halving measurements; inverse outcomes may differ. -/
theorem StepLayout.swapScaleStep_run (L : StepLayout) (h : L.Valid)
    (p : Nat) (st : ZState) (hi : Inv p st) (hfit : L.Fits st)
    (U : ModUnaryLayout) (n r : Nat) (hw : U.Widths n)
    (hnd : (L.history.active::U.wires).Nodup) (hsep : List.Disjoint U.wires L.used)
    (hp : p%2=1) (hpn : p<2^n) (hr : r<p)
    (s : State) (m : List Bool) (cursor : Nat) (hs : L.Ready st s.basis)
    (hz : regValue U.z s.basis=r) (hwork : regValue U.work s.basis=0) :
    let out := runWithTape (L.swapScaleStep U p cursor) m cursor s
    out.phase=s.phase ∧ regValue U.z out.basis=(if activeControl st then halveMod p r else r) ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  let t := run L.program (m.drop cursor) s
  let ordinal := cursor+measurementCount L.program
  let u := runWithTape (forgetBranch L.history.swap) m ordinal t
  let v := run (reverseHalf L.history.active U p) (m.drop (ordinal+1)) u
  have hq : L.history.swap∈L.used := by simp [used,histories,StepHistory.wires]
  have keep (q : Wire) (hqU : q∈U.wires) : u.basis q=s.basis q := by
    have he : q≠L.history.swap := fun he => List.disjoint_left.mp hsep hqU (he ▸ hq)
    simp only [u,forgetBranch_run]
    rw [show writeBit t.basis L.history.swap false q=t.basis q by simp [writeBit,he]]
    exact run_preserves_outside _ _ _ q (fun hm =>
      List.disjoint_left.mp hsep hqU (List.mem_toFinset.mp (L.program_support h hm)))
  have val (xs : List Wire) (hx : xs⊆U.wires) : regValue xs u.basis=regValue xs s.basis := by
    apply (regValue_eq_iff _ _ _).mpr
    intro q hq'
    exact keep q (hx hq')
  have huz := (val U.z (List.subset_append_left _ _)).trans hz
  have huw := (val U.work (List.subset_append_right _ _)).trans hwork
  have ha : u.basis L.history.active=activeControl st := by
    have he := (L.swapDecoder_distinct h).1
    simp only [u,forgetBranch_run]
    rw [show writeBit t.basis L.history.swap false L.history.active=t.basis L.history.active by
      simp [writeBit,he]]
    exact (L.program_zSlot_controls h st hfit s (m.drop cursor) hs.1 hs.2.1 hs.2.2.1).2.2.2.1
  have hv := reverseHalf_spec L.history.active U n p r (activeControl st) hw hnd hp hpn hr
    u (m.drop (ordinal+1)) ⟨⟨ha,huz⟩,huw⟩
  have frame (q : Wire) (ho : q∉U.z) : v.basis q=u.basis q :=
    controlledHalf_frame L.history.active U n p r (activeControl st) hw hnd hp hpn hr
      u (m.drop (ordinal+1)) ha huz huw q ho
  have hpi : (p : Int)%2=1 := by omega
  have hh := L.swapAround_run h p st hi hpi hfit U.z
    (List.disjoint_append_left.mp hsep).1 (embedRecorded (reverseHalf L.history.active U p))
    s m cursor hs (by simpa only [runWithTape_embedRecorded] using hv.1)
    (by simpa only [runWithTape_embedRecorded] using frame)
  dsimp only at hh ⊢
  change (runWithTape (L.swapScaleStep U p cursor) m cursor s).phase=s.phase ∧ _ at hh
  refine ⟨hh.1,?_,?_,hh.2.1⟩
  · have he : regValue U.z (runWithTape (L.swapScaleStep U p cursor) m cursor s).basis=
        regValue U.z v.basis := by
      apply (regValue_eq_iff _ _ _).mpr
      intro q hq'
      simpa only [runWithTape_embedRecorded] using hh.2.2 q hq'
    exact he.trans hv.2.1.2
  · have he : regValue U.work (runWithTape (L.swapScaleStep U p cursor) m cursor s).basis=
        regValue U.work s.basis := by
      apply (regValue_eq_iff _ _ _).mpr
      intro q hq'
      have hd := (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).2.2
      exact hh.2.1 q (fun hz' => List.disjoint_left.mp hd hz' hq')
    exact he.trans hwork

theorem StepLayout.swapScaleStep_wellFormed (L : StepLayout) (U : ModUnaryLayout) (p cursor : Nat) :
    RecordedWellFormedAt cursor (L.swapScaleStep U p cursor) :=
  L.swapAround_wellFormed _ cursor (embedRecorded_wellFormed _ _)

theorem StepLayout.swapScaleStep_counts (L : StepLayout) (h : L.Valid)
    (n v k a p cursor : Nat) (hw : L.Sized n v k) (U : ModUnaryLayout)
    (hu : U.Widths a) (ha : 0<a) :
    recordedToffoliCount (L.swapScaleStep U p cursor)=2*(5*n+5*v+k-4)+1+(3*a+2) ∧
    recordedMeasurementCount (L.swapScaleStep U p cursor)=2*(4*n+3*v+k-5)+1+2*a := by
  have hh := L.swapAround_counts h n v k hw (embedRecorded (reverseHalf L.history.active U p)) cursor
  simpa only [swapScaleStep,(embedRecorded_counts _).1,(embedRecorded_counts _).2,
    (reverseHalf_counts L.history.active U a p hu ha).1,
    (reverseHalf_counts L.history.active U a p hu ha).2] using hh

end ECDSAAdd.Arithmetic.Divsteps
