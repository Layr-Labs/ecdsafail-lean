import ECDSAAdd.Arithmetic.Paper935.FusedMagnitudeProgram
import ECDSAAdd.Arithmetic.Paper935.FusedEndpointModel

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] lift24Program magnitudeWindow signComplement

private theorem window_pull_value (s : State) :
    regValue lift24Word (pullState magnitudeWindowMap s).basis=regValue lift24Word s.basis := by
  apply regValue_congr
  intro q hq
  have bound : q<59 := by
    simp only [lift24Word,List.mem_range'] at hq
    dsimp only [Wire] at *
    omega
  simp [pullState,magnitudeWindowMap,bound]

theorem magnitudeWindow_contract (subtract : Bool) (s : State) (m : List Bool)
    (ready : MagnitudeReady s.basis) :
    let out := run (magnitudeWindow subtract) m s
    regValue lift24Word out.basis=
      (regValue lift24Word s.basis+(if s.basis 0 then lift24Literal subtract else 0))%2^58 ∧
    MagnitudeReady out.basis ∧ out.basis 0=s.basis 0 ∧ out.phase=s.phase := by
  have clean : Lift24Ready 0 (pullState magnitudeWindowMap s).basis := by
    intro i hi _
    simpa [pullState,magnitudeWindowMap,show ¬59+i<59 by omega,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using ready i hi
  have h := lift24Program_contract subtract (pullState magnitudeWindowMap s) m clean
  have execution := run_rename magnitudeWindowMap magnitudeWindowMap_injective (lift24Program subtract) m s
  rw [←magnitudeWindow] at execution
  dsimp only at h
  rw [←execution,window_pull_value,window_pull_value] at h
  refine ⟨h.1,?_,h.2.2.1,h.2.2.2⟩
  intro i hi
  dsimp only [Wire] at i hi
  have pool := h.2.1 i hi (Nat.zero_le _)
  simpa [pullState,magnitudeWindowMap,show ¬59+i<59 by omega,Nat.add_assoc,
    Nat.add_comm,Nat.add_left_comm] using pool

theorem magnitudeWindow_high_frame (subtract : Bool) (s : State) (m : List Bool)
    (q : Wire) (lo : 59≤q) (hi : q<281) :
    (run (magnitudeWindow subtract) m s).basis q=s.basis q := by
  apply run_preserves_outside
  rw [magnitudeWindow,renameProgram_support]
  intro mem
  obtain ⟨j,_,eq⟩ := Finset.mem_image.mp mem
  dsimp [magnitudeWindowMap] at eq
  dsimp only [Wire] at *
  split_ifs at eq <;> omega

theorem magnitudeWindow_increment (s : State) (m : List Bool)
    (ready : MagnitudeReady s.basis)
    (nowrap : s.basis 0=true → regValue lift24Word s.basis+1<2^58) :
    regValue magnitudePayload (run (magnitudeWindow false) m s).basis=
      regValue magnitudePayload s.basis+(s.basis 0).toNat := by
  have low := (magnitudeWindow_contract false s m ready).1
  have small : regValue lift24Word s.basis+(s.basis 0).toNat<2^58 := by
    cases h : s.basis 0
    · simpa only [h,Bool.toNat_false,Nat.add_zero,lift24Word,List.length_range']
        using regValue_lt lift24Word s.basis
    · simpa only [h,Bool.toNat_true] using nowrap h
  have lv : regValue lift24Word (run (magnitudeWindow false) m s).basis=
      regValue lift24Word s.basis+(s.basis 0).toNat := by
    rw [low]
    have flag : (if s.basis 0 then lift24Literal false else 0)=(s.basis 0).toNat := by
      cases s.basis 0 <;> rfl
    rw [flag,Nat.mod_eq_of_lt small]
  have high : regValue (List.range' 59 222) (run (magnitudeWindow false) m s).basis=
      regValue (List.range' 59 222) s.basis := by
    apply regValue_congr
    intro q hq
    simp only [List.mem_range'] at hq
    obtain ⟨i,hi,rfl⟩ := hq
    exact magnitudeWindow_high_frame false s m _ (by dsimp only [Wire]; omega)
      (by dsimp only [Wire] at *; omega)
  have split : magnitudePayload=lift24Word++List.range' 59 222 := by decide +kernel
  rw [split,regValue_append,regValue_append,lv,high]
  omega

private theorem magnitude_low_mod (s : BasisState) :
    regValue lift24Word s=regValue magnitudePayload s%2^58 := by
  have split : magnitudePayload=lift24Word++List.range' 59 222 := by decide +kernel
  have small : regValue lift24Word s<2^58 := by
    simpa only [lift24Word,List.length_range'] using regValue_lt lift24Word s
  rw [split,regValue_append]
  change _=(_+2^58*_)%2^58
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small]

/-- Exact unsigned magnitude formula for the emitted 280-bit lift, under
its low-window no-wrap condition. The sign bit itself is retained. -/
theorem fusedMagnitudeLift_value (s : State) (m : List Bool)
    (ready : MagnitudeReady s.basis)
    (nowrap : s.basis 0=true →
      (2^280-1-regValue magnitudePayload s.basis)%2^58+1<2^58) :
    regValue magnitudePayload (run (fusedMagnitudeLift false) m s).basis=
      if s.basis 0 then 2^280-regValue magnitudePayload s.basis
      else regValue magnitudePayload s.basis := by
  let t := run (signComplement 0 magnitudePayload) m s
  have comp := signComplement_correct 0 magnitudePayload
    (by exact List.nodup_range') (by simp [magnitudePayload]) s m
  have control : t.basis 0=s.basis 0 := comp.2.1 0 (by simp [magnitudePayload])
  have clean : MagnitudeReady t.basis := by
    intro i hi
    rw [comp.2.1 (281+i) (by simp [magnitudePayload])]
    exact ready i hi
  have window : t.basis 0=true → regValue lift24Word t.basis+1<2^58 := by
    intro enabled
    have hs := control.symm.trans enabled
    rw [magnitude_low_mod,comp.2.2]
    simpa only [hs,if_true,magnitudePayload,List.length_range'] using nowrap hs
  have result := magnitudeWindow_increment t m clean window
  have bound : regValue magnitudePayload s.basis<2^280 := by
    simpa only [magnitudePayload,List.length_range'] using regValue_lt magnitudePayload s.basis
  simp only [fusedMagnitudeLift,Bool.false_eq_true,if_false,run_append,run_take]
  simp only [(signComplement_counts 0 magnitudePayload).2,List.drop_zero]
  rw [result,comp.2.2,control]
  have len : magnitudePayload.length=280 := by simp [magnitudePayload]
  rw [len]
  cases s.basis 0 <;> simp only [Bool.false_eq_true,if_false,if_true,Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
  omega

theorem fusedMagnitudeLift_cleanup (s : State) (m : List Bool)
    (ready : MagnitudeReady s.basis) :
    let out := run (fusedMagnitudeLift false) m s
    MagnitudeReady out.basis ∧ out.basis 0=s.basis 0 ∧ out.phase=s.phase := by
  let t := run (signComplement 0 magnitudePayload) m s
  have comp := signComplement_correct 0 magnitudePayload
    (by exact List.nodup_range') (by simp [magnitudePayload]) s m
  have clean : MagnitudeReady t.basis := by
    intro i hi
    rw [comp.2.1 (281+i) (by simp [magnitudePayload])]
    exact ready i hi
  have h := magnitudeWindow_contract false t m clean
  simp only [fusedMagnitudeLift,Bool.false_eq_true,if_false,run_append,run_take]
  simp only [(signComplement_counts 0 magnitudePayload).2,List.drop_zero]
  exact ⟨h.2.1,h.2.2.1.trans (comp.2.1 0 (by simp [magnitudePayload])),h.2.2.2.trans comp.1⟩

/-- Physical two's-complement input convention, with separate retained sign. -/
def MagnitudeEncodes (z : Int) (s : BasisState) : Prop :=
  s 0=decide (z<0) ∧ regValue magnitudePayload s=
    if z<0 then 2^280-z.natAbs else z.natAbs

/-- The model's LiftGood condition suffices for the actual 280-bit lift.
The input encoding is explicit; it is not inferred from measured data. -/
theorem fusedMagnitudeLift_of_good (call : FusedCall) (s : State) (m : List Bool)
    (ready : MagnitudeReady s.basis) (encoding : MagnitudeEncodes call.coefficient s.basis)
    (good : call.LiftGood) :
    regValue magnitudePayload (run (fusedMagnitudeLift false) m s).basis=call.coefficient.natAbs := by
  obtain ⟨sign,payload⟩ := encoding
  obtain ⟨bound,window⟩ := good
  have nowrap : s.basis 0=true →
      (2^280-1-regValue magnitudePayload s.basis)%2^58+1<2^58 := by
    intro enabled
    have neg : call.coefficient<0 := by simpa only [sign,decide_eq_true_eq] using enabled
    rw [payload,if_pos neg]
    have complement : 2^280-1-(2^280-call.coefficient.natAbs)=call.coefficient.natAbs-1 := by omega
    rw [complement]
    exact window neg
  rw [fusedMagnitudeLift_value s m ready nowrap,sign,payload]
  by_cases neg : call.coefficient<0
  · simp only [neg,decide_true,if_true]
    omega
  · simp only [neg,decide_false,Bool.false_eq_true,if_false]

end ECDSAAdd.Arithmetic.Paper935
