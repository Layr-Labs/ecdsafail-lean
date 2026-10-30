import ECDSAAdd.Submission.Entrant.FrontierEntry1591FieldFrames
import ECDSAAdd.Submission.Entrant.FrontierEntry1591EntryFrame

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry1591Field
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires

private theorem double_half_div (Y W : Fp) : 2*(Y/2/W)=Y/W := by
  have two : (2:Fp)≠0 := by decide
  rw [div_div,mul_comm (2:Fp) W,←div_div,mul_div_cancel₀ _ two]

private theorem restore_origin (origin : BasisState) :
    writeBit (writeBit origin (base 2400) true) (base 2400) (origin (base 2400))=origin := by
  funext q
  by_cases eq : q=base 2400
  · subst q;simp only [writeBit,Function.update_self]
  · simp only [writeBit,Function.update_of_ne eq]

private theorem canonical_unforce (P : Program) (off : base 2400∉wires P)
    (origin : BasisState) (s forced : State) (m : List Bool)
    (forceEq : forced=⟨s.phase,writeBit s.basis (base 2400) true⟩)
    (B : Fp) (control : s.basis (base 2400)=origin (base 2400))
    (result : (run P m forced).phase=forced.phase ∧
      NewFieldFrameOB5.EncodedCanonicalFrame (writeBit origin (base 2400) true) B 0 (run P m forced)) :
    (run P m s).phase=s.phase ∧ NewFieldFrameOB5.EncodedCanonicalFrame origin B 0 (run P m s) := by
  subst forced
  have back := FrontierEntry1591.canonical_control_set (writeBit origin (base 2400) true) B 0
    (run P m ⟨s.phase,writeBit s.basis (base 2400) true⟩) (origin (base 2400)) result.2
  have undo := FrontierEntry1591.run_control_unset P off s m true
  refine ⟨(congrArg State.phase undo).trans result.1,?_⟩
  rw [undo]
  simpa only [restore_origin,control] using back

private theorem field_unforce (P : Program) (off : base 2400∉wires P)
    (origin : BasisState) (s forced : State) (m : List Bool)
    (forceEq : forced=⟨s.phase,writeBit s.basis (base 2400) true⟩)
    (B : Fp) (control : s.basis (base 2400)=origin (base 2400))
    (result : (run P m forced).phase=forced.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame (writeBit origin (base 2400) true) B 0 (run P m forced)) :
    (run P m s).phase=s.phase ∧ NewFieldFrameOB5.EncodedFieldFrame origin B 0 (run P m s) := by
  subst forced
  have back := FrontierEntry1591.frame_control_set (writeBit origin (base 2400) true) B 0
    (run P m ⟨s.phase,writeBit s.basis (base 2400) true⟩) (origin (base 2400)) result.2
  have undo := FrontierEntry1591.run_control_unset P off s m true
  refine ⟨(congrArg State.phase undo).trans result.1,?_⟩
  rw [undo]
  simpa only [restore_origin,control] using back

theorem entry_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedFieldFrame origin (Y/2) 0 s)
    (in511 : s.basis (base 511)=true) (in1542 : s.basis (base 1542)=false)
    (workIn : s.basis work=false)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (run entry m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedCanonicalFrame origin (Y/(x:Fp)) 0 (run entry m s) := by
  let origin' := writeBit origin (base 2400) true
  let forced : State := ⟨s.phase,writeBit s.basis (base 2400) true⟩
  have ctx' := FrontierEntry1591.context_control_set origin ctx true
  have ha' := FrontierEntry1591.source_zero_control_set origin true ha
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)) := by
    rw [FrontierEntry1591.trace_control_set]
    exact trace
  have input' := FrontierEntry1591.frame_control_set origin (Y/2) 0 s true input
  have parity' := FrontierEntry1591.parity_host_control_set controls host (by decide)
    controls_away_control s true parity
  have result := entry_core_frame origin' ctx' ha' x hx0 hx trace' (Y/2) forced m
    (by simp only [forced,writeBit,Function.update_self]) input'
    (by simpa only [forced,writeBit,Function.update_of_ne (show base 511≠base 2400 from by decide)] using in511)
    (by simpa only [forced,writeBit,Function.update_of_ne (show base 1542≠base 2400 from by decide)] using in1542)
    (by simpa only [forced,writeBit,Function.update_of_ne (show work≠base 2400 from by decide)] using workIn)
    parity'
  have value : 2*(if origin' (base 2400) then Y/2/(x:Fp) else Y/2)=Y/(x:Fp) := by
    simp only [origin',writeBit,Function.update_self,if_true]
    exact double_half_div Y (x:Fp)
  rw [value] at result
  have control : s.basis (base 2400)=origin (base 2400) := by
    have bit := field_special_at origin (Y/2) 0 s 2400 (by simp) input
    rwa [OneFlagSW.selSig_2400] at bit
  exact canonical_unforce entry entry_control_away origin s forced m rfl (Y/(x:Fp)) control result

theorem exit_frame (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 s)
    (in511 : s.basis (base 511)=true) (in1542 : s.basis (base 1542)=false)
    (workIn : s.basis work=false)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (run exit m s).phase=s.phase ∧
      NewFieldFrameOB5.EncodedFieldFrame origin (Y*(x:Fp)/2) 0 (run exit m s) := by
  let origin' := writeBit origin (base 2400) true
  let forced : State := ⟨s.phase,writeBit s.basis (base 2400) true⟩
  have ctx' := FrontierEntry1591.context_control_set origin ctx true
  have ha' := FrontierEntry1591.source_zero_control_set origin true ha
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)) := by
    rw [FrontierEntry1591.trace_control_set]
    exact trace
  have input' := FrontierEntry1591.canonical_control_set origin Y 0 s true input
  have parity' := FrontierEntry1591.parity_host_control_set controls host (by decide)
    controls_away_control s true parity
  have result := exit_core_frame origin' ctx' ha' x hx0 hx trace' Y forced m
    (by simp only [forced,writeBit,Function.update_self]) input'
    (by simpa only [forced,writeBit,Function.update_of_ne (show base 511≠base 2400 from by decide)] using in511)
    (by simpa only [forced,writeBit,Function.update_of_ne (show base 1542≠base 2400 from by decide)] using in1542)
    (by simpa only [forced,writeBit,Function.update_of_ne (show work≠base 2400 from by decide)] using workIn)
    parity'
  have value : (if origin' (base 2400) then Y/2*(x:Fp) else Y/2)=Y*(x:Fp)/2 := by
    simp only [origin',writeBit,Function.update_self,if_true,div_eq_mul_inv]
    ring
  rw [value] at result
  have control : s.basis (base 2400)=origin (base 2400) := by
    have bit := canonical_special_at origin Y 0 s 2400 (by simp) input
    rwa [OneFlagSW.selSig_2400] at bit
  exact field_unforce exit exit_control_away origin s forced m rfl (Y*(x:Fp)/2) control result

theorem entry_result (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (virtual actual : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 virtual)
    (phase : actual.phase=virtual.phase)
    (same : ∀q,q∉numerator → actual.basis q=virtual.basis q)
    (half : regValue numerator actual.basis=centerWord (Y/2))
    (in511 : actual.basis (base 511)=true) (in1542 : actual.basis (base 1542)=false)
    (workIn : actual.basis work=false)
    (parity : actual.basis host=TraceParity5.parity (controls.map actual.basis)) :
    (run entry m actual).phase=actual.phase ∧
      regValue numerator (run entry m actual).basis=(Y/(x:Fp)).val ∧
      ∀q,q∉numerator → (run entry m actual).basis q=actual.basis q := by
  have fieldInput := FrontierEntry1591EntryFrame.canonical_to_field ctx.hn origin ctx.parity ctx.env.2.2
    Y virtual actual phase same half input
  have result := entry_frame origin ctx ha x hx0 hx trace Y actual m fieldInput in511 in1542 workIn parity
  exact ⟨result.1,canonical_numerator_value origin ctx _ _ result.2,
    field_canonical_outside origin ctx ha _ _ actual _ fieldInput result.2 result.1⟩

theorem exit_result (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 s)
    (in511 : s.basis (base 511)=true) (in1542 : s.basis (base 1542)=false)
    (workIn : s.basis work=false)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis)) :
    (run exit m s).phase=s.phase ∧
      regValue numerator (run exit m s).basis=centerWord (Y*(x:Fp)/2) ∧
      ∀q,q∉numerator → (run exit m s).basis q=s.basis q := by
  have result := exit_frame origin ctx ha x hx0 hx trace Y s m input in511 in1542 workIn parity
  exact ⟨result.1,field_numerator_value origin _ _ _ result.2,
    canonical_field_outside origin ctx ha _ _ s _ input result.2 result.1⟩

end ECDSAAdd.Entrant.FrontierEntry1591Field
