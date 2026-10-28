import ECDSAAdd.Arithmetic.NativeFirstDirectLayout
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open RecordedQuantum

theorem adds_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (inv : Bool) :
    GatePhysical (hAdd w inv) ∧ GatePhysical (kAdd w inv) := by
  have h : GatePhysical (hAdd w inv) := by
    apply mappedAdd_physical _ _ _ _ (h_inputs_nd w hn)
    intro b hb q hq
    apply h_sources_fresh w hn inv q
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  have k : GatePhysical (mappedAdd (kBits w inv) (wireBlock w 771 257) (wireBlock w 1540 256) (w 770)) := by
    apply mappedAdd_physical _ _ _ _ (k_inputs_nd w hn)
    intro b hb q hq
    apply k_sources_fresh w hn inv q
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  refine ⟨h,?_⟩
  rw [kAdd,gatePhysical_append]
  exact ⟨k,by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

theorem programs_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (forward w) ∧ GatePhysical (inverse w) := by
  have cp : GatePhysical (lowCopy w) := copyRegister_physical none _ _ (copy_inputs_nd w hn) (by simp)
  have ro := rotate_physical (wireBlock w 770 258) (block_nodup w hn _ _ (by omega))
  have a := adds_physical w hn false
  have b := adds_physical w hn true
  have n1 := index_ne w hn 770 1028 (by omega) (by omega) (by omega)
  have n2 := index_ne w hn 1028 0 (by omega) (by omega) (by omega)
  have n3 := index_ne w hn 1028 770 (by omega) (by omega) (by omega)
  have pre : GatePhysical [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,n1,n2]
  have post : GatePhysical [.X (w 0),.CX (w 1028) (w 0),.CX (w 770) (w 1028)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,n1,n2]
  have mid : GatePhysical [.CX (w 1028) (w 770)] := by simp [GatePhysical,PhysicalInstr,ProperGate,n3]
  simp only [forward,inverse,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨pre,cp⟩,a.1⟩,mid⟩,ro.1⟩,a.2⟩,⟨⟨⟨⟨⟨b.2,ro.2⟩,mid⟩,b.1⟩,cp⟩,post⟩⟩
end ECDSAAdd.Arithmetic.NativeFirstDirect
