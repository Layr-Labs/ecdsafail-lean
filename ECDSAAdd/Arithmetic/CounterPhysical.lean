import ECDSAAdd.Arithmetic.Borrow
import ECDSAAdd.Arithmetic.ComparePhysical

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem fullAdder_physical (a b cin out carry : Wire)
    (hn : [a,b,cin,out,carry].Nodup) : GatePhysical (fullAdder a b cin out carry) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  simp_all [fullAdder,GatePhysical,PhysicalInstr,ProperGate]

theorem rippleAdder_physical (bs : List AddBit) (cin : Wire)
    (hn : (cin::addWires bs).Nodup) : GatePhysical (rippleAdder bs cin) := by
  induction bs generalizing cin with
  | nil => simp [rippleAdder,GatePhysical]
  | cons b bs ih =>
    have hsmall : [b.x,b.y,cin,b.out,b.carry].Nodup := by
      have h := hn
      simp only [addWires,List.nodup_cons,List.mem_cons,not_or] at h
      simp_all [ne_comm]
    have ht : (b.carry::addWires bs).Nodup := by
      change (cin::b.x::b.y::b.out::b.carry::addWires bs).Nodup at hn
      exact hn.tail.tail.tail.tail
    simp only [rippleAdder,gatePhysical_append]
    exact ⟨⟨fullAdder_physical _ _ _ _ _ hsmall,ih _ ht⟩,eraseCarry_physical _ _ _ _⟩

theorem add_physical (L : AdderLayout) (hn : L.wires.Nodup) : GatePhysical (add L) :=
  rippleAdder_physical L.bits L.cin hn

theorem counterXor_physical (L : AdderLayout) (hn : L.wires.Nodup) :
    GatePhysical (counterIncXor L) ∧ GatePhysical (counterDecXor L) := by
  constructor
  · exact add_physical L hn
  · change GatePhysical (notRegister (L.cin::L.y) ++ add L ++ notRegister (L.cin::L.y))
    simp only [gatePhysical_append]
    exact ⟨⟨notRegister_physical _,add_physical L hn⟩,notRegister_physical _⟩

theorem counters_physical (L : AdderLayout) (hn : L.wires.Nodup) :
    GatePhysical (counterInc L) ∧ GatePhysical (counterDec L) := by
  have h := counterXor_physical L hn
  have hs := counterXor_physical L.swapCounter (L.swapCounter_perm.nodup_iff.mpr hn)
  simp only [counterInc,counterDec,gatePhysical_append]
  exact ⟨⟨h.1,hs.2⟩,⟨h.2,hs.1⟩⟩

theorem compareLtConst_physical (control : Option Wire) (x T carry : List Wire)
    (cin target K : Nat) (hn : (target::cin::x++T++carry).Nodup)
    (hc : ∀ c ∈ control, c ≠ target) :
    GatePhysical (compareLtConst control x T carry cin target K) := by
  simp only [compareLtConst,gatePhysical_append]
  exact ⟨⟨xorConstant_physical _ _,compareLt_physical _ _ _ _ _ _ hn hc⟩,
    xorConstant_physical _ _⟩

theorem counterActiveXor_physical (L : AdderLayout) (target i : Nat)
    (hnd : (target::L.wires).Nodup) : GatePhysical (counterActiveXor L target i) := by
  have hs : (target::L.cin::(L.x++L.y++L.carry)).Nodup := by
    have hn := List.Perm.nodup_iff (List.Perm.cons target L.interface_perm)
    have h := hn.mpr hnd
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp h w
    simp only [List.count_cons,List.count_append] at hc ⊢
    omega
  simp only [counterActiveXor,gatePhysical_append]
  exact ⟨compareLtConst_physical _ _ _ _ _ _ _ hs (by simp),
    by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

end ECDSAAdd.Arithmetic
