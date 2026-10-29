import ECDSAAdd.Arithmetic.MappedKernelPhysical
import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites
import ECDSAAdd.Challenge.Contract

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic.MappedCompressed.LaneA
open Secp256k1 RecordedQuantum

/-- Repair only an inactive divisor whose two low bits are zero. -/
def controlRepairBit (s : BasisState) : Bool :=
  !s (base 2400) && !s (base 770) && !s (base 771)

def controlRepairState (s : State) : State :=
  ⟨s.phase,writeBit (writeBit s.basis (base 2411) (controlRepairBit s.basis))
    (base 770) (s.basis (base 770) ^^ controlRepairBit s.basis)⟩

def controlRepairEnter : Program :=
  [.X (base 2400),.X (base 770),.X (base 771),
   .CCX (base 770) (base 771) (base 0),
   .CCX (base 2400) (base 0) (base 2411),
   .measureX (base 0) [] [.CZ (base 770) (base 771)],
   .X (base 771),.X (base 770),.X (base 2400),
   .CX (base 2411) (base 770)]

def controlRepairLeave : Program :=
  [.CX (base 2411) (base 770),
   .X (base 2400),.X (base 770),.X (base 771),
   .CCX (base 770) (base 771) (base 0),
   .measureX (base 2411) [] [.CZ (base 2400) (base 0)],
   .measureX (base 0) [] [.CZ (base 770) (base 771)],
   .X (base 771),.X (base 770),.X (base 2400)]

def controlRepair (kernel : Program) : Program :=
  controlRepairEnter ++ (kernel ++ controlRepairLeave)

/-- Every record gives the same repaired state, with phase restored. -/
theorem controlRepairEnter_run (s : State) (m : List Bool)
    (ht : s.basis (base 0)=false) (hf : s.basis (base 2411)=false) :
    run controlRepairEnter m s=controlRepairState s := by
  simp only [base] at ht hf
  cases he : s.basis 2416 <;> cases ha : s.basis 786 <;> cases hb : s.basis 787 <;>
    cases hm : m.head?.getD false
  all_goals
    simp [controlRepairEnter,controlRepairState,controlRepairBit,run,measureAndCorrect,
      correct,writeBit,base,he,ha,hb,hm,ht,hf]
  all_goals
    funext q
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-- The divisor is restored before either measured flag is erased. -/
theorem controlRepairLeave_run (s : State) (m : List Bool)
    (ht : s.basis (base 0)=false) (hf : s.basis (base 2411)=false) :
    run controlRepairLeave m (controlRepairState s)=s := by
  simp only [base] at ht hf
  cases he : s.basis 2416 <;> cases ha : s.basis 786 <;> cases hb : s.basis 787 <;>
    cases hm : m.head?.getD false <;> cases hn : m[1]?.getD false
  all_goals
    simp [controlRepairLeave,controlRepairState,controlRepairBit,run,measureAndCorrect,
      correct,writeBit,base,he,ha,hb,hm,hn,ht,hf]
  all_goals
    cases s
    congr 1
    funext q
    simp only [Function.update_apply]
    split_ifs <;> simp_all

theorem controlRepair_counts (kernel : Program) :
    toffoliCount (controlRepair kernel)=toffoliCount kernel+3 ∧
    measurementCount (controlRepair kernel)=measurementCount kernel+3 := by
  simp [controlRepair,controlRepairEnter,controlRepairLeave,toffoliCount_append,
    measurementCount_append,toffoliCount,measurementCount]
  omega

theorem controlRepair_support (kernel : Program) :
    wires (controlRepair kernel)⊆
      {base 2400,base 770,base 771,base 0,base 2411} ∪ wires kernel := by
  simp [controlRepair,controlRepairEnter,controlRepairLeave,wires_append,wires,Instr.wires,
    correctionWires,Finset.insert_subset_iff]
  intro q hq
  simp only [Finset.mem_insert]
  tauto

theorem controlRepair_physical (kernel : Program) (hk : GatePhysical kernel) :
    GatePhysical (controlRepair kernel) := by
  simp only [controlRepair,gatePhysical_append]
  refine ⟨?_,hk,?_⟩
  all_goals simp [controlRepairEnter,controlRepairLeave,GatePhysical,PhysicalInstr,ProperGate,base]

open Challenge in
theorem controlRepair_gateSlots (kernel : Program) :
    gateSlots (controlRepair kernel)=gateSlots kernel+23 := by
  simp [controlRepair,controlRepairEnter,controlRepairLeave,gateSlots_append,gateSlots,
    instructionSlots]
  omega

def controlRepairDivisor (b : Bool) (x : Nat) : Nat :=
  if b=false ∧ x%4=0 then x+1 else x

theorem controlRepairDivisor_pos (b : Bool) (x : Nat) (hz : x=0 → b=false) :
    0<controlRepairDivisor b x := by
  unfold controlRepairDivisor
  split_ifs with h
  · omega
  · by_contra he
    have hx : x=0 := by omega
    exact h ⟨hz hx,by rw [hx]⟩

theorem controlRepairDivisor_lt (b : Bool) (x : Nat) (hx : x<p) :
    controlRepairDivisor b x<p := by
  have hp4 : p%4=3 := by decide
  unfold controlRepairDivisor
  split_ifs with h
  · omega
  · exact hx

private theorem controlRepair_low_value (b a c : Bool) (t : Nat) :
    let x := a.toNat+2*(c.toNat+2*t)
    (a ^^ (!b && !a && !c)).toNat+2*(c.toNat+2*t) = controlRepairDivisor b x := by
  dsimp
  have rem : (a.toNat+2*(c.toNat+2*t))%4=a.toNat+2*c.toNat := by
    cases a <;> cases c <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
  rw [controlRepairDivisor,rem]
  cases b <;> cases a <;> cases c <;> simp [Bool.toNat,Nat.add_comm]

theorem controlRepairState_outside (s : State) (q : Wire)
    (hf : q≠base 2411) (ha : q≠base 770) :
    (controlRepairState s).basis q=s.basis q := by
  simp [controlRepairState,writeBit,hf,ha]

theorem controlRepairState_divisor (s : State) :
    regValue (wireBlock base 770 256) (controlRepairState s).basis=
      controlRepairDivisor (s.basis (base 2400)) (regValue (wireBlock base 770 256) s.basis) := by
  have split : wireBlock base 770 256=base 770::base 771::wireBlock base 772 254 := rfl
  have tail : regValue (wireBlock base 772 254) (controlRepairState s).basis=
      regValue (wireBlock base 772 254) s.basis := by
    apply regValue_congr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    apply controlRepairState_outside
    all_goals intro eq; have same := base_injective eq; omega
  rw [split]
  change (if (controlRepairState s).basis (base 770) then 1 else 0)+
      2*((if (controlRepairState s).basis (base 771) then 1 else 0)+
        2*regValue (wireBlock base 772 254) (controlRepairState s).basis)=
    controlRepairDivisor (s.basis (base 2400))
      ((if s.basis (base 770) then 1 else 0)+2*((if s.basis (base 771) then 1 else 0)+
        2*regValue (wireBlock base 772 254) s.basis))
  rw [tail]
  simpa [controlRepairState,controlRepairBit,writeBit,base,Bool.toNat,Bool.cond_eq_ite] using
    controlRepair_low_value (s.basis (base 2400)) (s.basis (base 770)) (s.basis (base 771))
      (regValue (wireBlock base 772 254) s.basis)

/-- A numerator-only kernel preserves the repair bits. All records are independent. -/
theorem controlRepair_states (kernel : Program) (ys : List Wire)
    (away : ∀q∈[base 2400,base 770,base 771,base 0,base 2411],q∉ys)
    (s : State) (enterRecord kernelRecord leaveRecord : List Bool) (R : Nat)
    (ht : s.basis (base 0)=false) (hf : s.basis (base 2411)=false)
    (hk : let u := run kernel kernelRecord (controlRepairState s)
      u.phase=s.phase ∧ regValue ys u.basis=R ∧
      ∀q,q∉ys → u.basis q=(controlRepairState s).basis q) :
    let t := run controlRepairEnter enterRecord s
    let u := run kernel kernelRecord t
    let v := run controlRepairLeave leaveRecord u
    v.phase=s.phase ∧ regValue ys v.basis=R ∧ ∀q,q∉ys → v.basis q=s.basis q := by
  dsimp only
  rw [controlRepairEnter_run s enterRecord ht hf]
  let u := run kernel kernelRecord (controlRepairState s)
  let v : State := ⟨s.phase,fun q => if q∈ys then u.basis q else s.basis q⟩
  have old (q : Wire) (hq : q∈[base 2400,base 770,base 771,base 0,base 2411]) :
      v.basis q=s.basis q := by
    simp only [v,if_neg (away q hq)]
  have bit : controlRepairBit v.basis=controlRepairBit s.basis := by
    simp only [controlRepairBit,old (base 2400) (by simp),old (base 770) (by simp),
      old (base 771) (by simp)]
  have restore : controlRepairState v=u := by
    apply State.extensionality
    · exact hk.1.symm
    · funext q
      by_cases hy : q∈ys
      · have hqf : q≠base 2411 := fun eq => away _ (by simp) (eq ▸ hy)
        have hqa : q≠base 770 := fun eq => away _ (by simp) (eq ▸ hy)
        rw [controlRepairState_outside v q hqf hqa]
        simp only [v,if_pos hy]
      · rw [hk.2.2 q hy]
        simp only [controlRepairState]
        by_cases hqf : q=base 2411
        · subst q; simp [writeBit,base,bit]
        · by_cases hqa : q=base 770
          · subst q
            simp only [writeBit,Function.update_self]
            rw [old (base 770) (by simp),bit]
          · simp [writeBit,hqf,hqa,v,hy]
  have leave : run controlRepairLeave leaveRecord u=v := by
    rw [←restore]
    exact controlRepairLeave_run v leaveRecord
      ((old (base 0) (by simp)).trans ht) ((old (base 2411) (by simp)).trans hf)
  rw [leave]
  refine ⟨rfl,?_,?_⟩
  · exact (regValue_congr ys v.basis u.basis (by intro q hq; simp [v,hq])).trans hk.2.1
  · intro q hq; simp [v,hq]

end ECDSAAdd.Arithmetic.MappedCompressed.LaneA
