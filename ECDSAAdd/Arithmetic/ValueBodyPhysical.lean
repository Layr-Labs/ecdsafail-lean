import ECDSAAdd.Arithmetic.ValueBody
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem cswap_physical (c a b : Wire) (hn : [c,a,b].Nodup) : GatePhysical (cswap c a b) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  simp_all [cswap,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

theorem shifts_physical (c : Wire) (r : List Wire) (hn : (c::r).Nodup) :
    GatePhysical (shiftRight c r) ∧ GatePhysical (shiftLeft c r) := by
  induction r with
  | nil => simp [shiftRight,shiftLeft,GatePhysical]
  | cons a r ih =>
    cases r with
    | nil => simp [shiftRight,shiftLeft,GatePhysical]
    | cons b bs =>
      have hsmall : [c,a,b].Nodup := hn.sublist (by simp)
      have htail : (c::b::bs).Nodup := hn.sublist (by simp)
      have hrec := ih htail
      simpa only [shiftRight,shiftLeft,gatePhysical_append] using
        And.intro (And.intro (cswap_physical c a b hsmall) hrec.1)
          (And.intro hrec.2 (cswap_physical c a b hsmall))

theorem inplaceArithmetic_physical (L : RoundDataLayout) (c : Wire)
    (hnd : (c::L.wires).Nodup) (f g : RoundField)
    (hf : RoundDataLayout.DataField f) (hg : RoundDataLayout.DataField g) (hne : f≠g)
    (negative : Bool) : GatePhysical (inplaceArithmetic L f g c negative) := by
  have hn : (c::L.cin::(L.reg g++L.reg .y++L.reg f++(L.reg .carry).take (L.width-1))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h1 := L.source_adder_count f g hf hg hne w
    have h2 := (L.adder f).interface_perm.count_eq w
    have h3 := List.nodup_iff_count.mp hnd w
    have h4 := (List.take_sublist (L.width-1) (L.reg .carry)).count_le w
    simp only [List.count_append,List.count_cons,
      (L.adder_fields f).1,(L.adder_fields f).2.1,(L.adder_fields f).2.2.1,
      (L.adder_fields f).2.2.2.1,(L.adder_fields f).2.2.2.2.1] at h1 h2 h3 ⊢
    omega
  have h := measuredMasked_physical c L.cin (L.reg g) (L.reg .y) (L.reg f)
    ((L.reg .carry).take (L.width-1)) hn
  cases negative <;> simp only [inplaceArithmetic, Bool.false_eq_true, if_false, if_true]
  · exact h.1
  · exact h.2

theorem roundSwap_physical (L : RoundDataLayout) (c : Wire) (hnd : (c::L.wires).Nodup)
    (f g : RoundField) (hne : f≠g) : GatePhysical (swapRegisters c (L.reg f) (L.reg g)) := by
  have hh := List.nodup_cons.mp hnd
  have hr : (c::(L.reg f++L.reg g)).Nodup := List.nodup_cons.mpr
    ⟨by intro hm; simp only [List.mem_append] at hm; rcases hm with hm | hm
        exact hh.1 (L.reg_mem f hm)
        exact hh.1 (L.reg_mem g hm),
      List.nodup_append'.mpr ⟨L.reg_nodup hh.2 f,L.reg_nodup hh.2 g,L.reg_disjoint hh.2 f g hne⟩⟩
  exact swapRegisters_physical c _ _ hr

theorem valueBodies_physical (L : RoundDataLayout) (a s t : Wire)
    (hn : ([a,s,t]++L.wires).Nodup) :
    GatePhysical (valueBodyProgram L a s t) ∧ GatePhysical (valueUnbodyProgram L a s t) := by
  have ctl (c : Wire) (hc : c ∈ [a,s,t]) : (c::L.wires).Nodup := by
    have h := List.nodup_append'.mp hn
    exact List.nodup_cons.mpr ⟨List.disjoint_left.mp h.2.2 hc,h.2.1⟩
  have ha := ctl a (by simp)
  have hs := ctl s (by simp)
  have ht := ctl t (by simp)
  have hu : (a::L.reg .u).Nodup := List.nodup_cons.mpr
    ⟨fun h => (List.nodup_cons.mp ha).1 (L.reg_mem .u h),
      L.reg_nodup (List.nodup_cons.mp ha).2 .u⟩
  have sw := roundSwap_physical L s hs .u .v (by decide)
  have sh := shifts_physical a (L.reg .u) hu
  have ar (b : Bool) := inplaceArithmetic_physical L t ht .u .v
    (by simp [RoundDataLayout.DataField]) (by simp [RoundDataLayout.DataField]) (by decide) b
  simp only [valueBodyProgram,valueUnbodyProgram,gatePhysical_append]
  exact ⟨⟨⟨⟨sw,ar true⟩,sh.1⟩,sw⟩,⟨⟨⟨sw,sh.2⟩,ar false⟩,sw⟩⟩

end ECDSAAdd.Arithmetic
