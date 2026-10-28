import ECDSAAdd.Arithmetic.ZeroControl
import ECDSAAdd.Arithmetic.SignedWordBits
import ECDSAAdd.Arithmetic.Divsteps.DoubleRow

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Exact nonzero test with a temporary constant-one wire and measured AND
work. Only the activity target is changed; no truncated low-bit test is used. -/
def activityTag (one active : Wire) (bs : List ZeroBit) : Program :=
  [.X one] ++ (zeroControlled one active bs ++ [.X one,.X active])

theorem activityTag_correct (one active : Wire) (bs : List ZeroBit)
    (hn : (one::active::bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (ho : s.basis one=false)
    (hz : ∀ b∈bs, s.basis b.work=false) :
    run (activityTag one active bs) m s=
      ⟨s.phase,writeBit s.basis active
        (s.basis active ^^ decide (regValue (bs.map ZeroBit.input) s.basis≠0))⟩ := by
  have hoa : one≠active := by intro he; exact (List.nodup_cons.mp hn).1 (by simp [he])
  have hout (b : ZeroBit) (hb : b∈bs) : b.input≠one ∧ b.work≠one := by
    constructor <;> intro he <;> apply (List.nodup_cons.mp hn).1
    all_goals exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires,he]⟩)
  let t : State := ⟨s.phase,writeBit s.basis one true⟩
  have htwork : ∀ b∈bs,t.basis b.work=false := by
    intro b hb
    simpa [t,writeBit,(hout b hb).2] using hz b hb
  have htinput : bs.all (fun b => !t.basis b.input)=bs.all (fun b => !s.basis b.input) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro h b hb <;> simpa [t,writeBit,(hout b hb).1] using h b hb
  have hall : bs.all (fun b => !s.basis b.input)=
      decide (regValue (bs.map ZeroBit.input) s.basis=0) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq,regValue_zero]
    simp [List.all_eq_true]
  have hmid := zeroControlled_correct one active bs hn t m htwork
  rw [htinput,hall] at hmid
  have hfirst : run [.X one] m s=t := by simp [run,t,ho]
  rw [activityTag,run_append,run_take,hfirst]
  change run (zeroControlled one active bs ++ [.X one,.X active]) m t = _
  rw [run_append,run_take,hmid]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=active
  · subst w
    cases ha : s.basis active <;> by_cases hv : regValue (bs.map ZeroBit.input) s.basis=0 <;>
      simp [t,writeBit,hoa,hoa.symm,ha,hv]
  · by_cases hwo : w=one
    · subst w
      simp [t,writeBit,hoa,ho]
    · simp [t,writeBit,hw,hwo,hoa]

theorem activityTag_counts (one active : Wire) (bs : List ZeroBit) :
    toffoliCount (activityTag one active bs)=bs.length ∧
    measurementCount (activityTag one active bs)=bs.length := by
  have h := zeroControlled_counts one active bs
  simp [activityTag,toffoliCount_append,measurementCount_append,toffoliCount,
    measurementCount,h.1,h.2]

theorem signedRegValue_zero_iff (r : List Wire) (s : BasisState) :
    signedRegValue r s=0 ↔ regValue r s=0 := by
  have h := regValue_lt r s
  have hh : 0<(2^(r.length-1):Nat) := by positivity
  unfold signedRegValue signedDecode
  split <;> omega

/-- The activity tag is the actual mathematical frozen-walk predicate under
physical integer encoding, including zero and negative values. -/
theorem activityTag_zState (one active : Wire) (bs : List ZeroBit)
    (hn : (one::active::bs.flatMap ZeroBit.wires).Nodup)
    (st : ECDSAAdd.Divsteps.ZState) (s : State) (m : List Bool)
    (ho : s.basis one=false) (ha : s.basis active=false)
    (hz : ∀ b∈bs,s.basis b.work=false)
    (hg : signedRegValue (bs.map ZeroBit.input) s.basis=st.g) :
    (run (activityTag one active bs) m s).basis active=ECDSAAdd.Divsteps.activeControl st := by
  rw [activityTag_correct one active bs hn s m ho hz]
  simp only [writeBit,Function.update_apply,ite_true,ha,Bool.false_xor]
  unfold ECDSAAdd.Divsteps.activeControl
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have h := signedRegValue_zero_iff (bs.map ZeroBit.input) s.basis
  rw [hg] at h
  exact not_congr h.symm

theorem activityTag_wires (one active : Wire) (bs : List ZeroBit) :
    wires (activityTag one active bs)=(one::active::bs.flatMap ZeroBit.wires).toFinset := by
  rw [activityTag,wires_append,wires_append,zeroControlled_wires]
  ext w
  simp [wires,Instr.wires]
  tauto

theorem activityTag_qubits (one active : Wire) (bs : List ZeroBit)
    (hn : (one::active::bs.flatMap ZeroBit.wires).Nodup) :
    qubitCount (activityTag one active bs)=2*bs.length+2 := by
  rw [qubitCount,activityTag_wires,←zeroControlled_wires]
  exact (zeroControlled_resources one active bs hn).2.2

end ECDSAAdd.Arithmetic.Divsteps
