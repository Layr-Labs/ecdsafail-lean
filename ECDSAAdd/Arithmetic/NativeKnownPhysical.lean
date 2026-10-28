import ECDSAAdd.Arithmetic.NativeFirstKnownProgram
import ECDSAAdd.Arithmetic.NativeFirstPhysical
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical

namespace ECDSAAdd.Arithmetic.NativeFirstKnown
open NativeFirstDirect RecordedQuantum

 theorem hReceiver_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (hReceiver w) := by
  rw [hReceiver,sealedProgram_eq]
  apply KnownOutputAdder.program_physical
  · simp [hBits_length,wireBlock_length]
  · simp [desired_length,wireBlock_length]
  · simp [wireBlock_length]
  · exact h_inputs_nd w hn
  · intro b hb q hq
    apply h_sources_fresh w hn true q
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  · intro b hb q hq
    apply desired_fresh w hn q
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩

theorem inverse_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (inverse w) := by
  have ka := (adds_physical w hn true).2
  have hr := hReceiver_physical w hn
  have cp : GatePhysical (lowCopy w) := copyRegister_physical none _ _ (copy_inputs_nd w hn) (by simp)
  have ro := (rotate_physical (wireBlock w 770 258) (block_nodup w hn _ _ (by omega))).2
  have n1 := index_ne w hn 770 1028 (by omega) (by omega) (by omega)
  have n2 := index_ne w hn 1028 0 (by omega) (by omega) (by omega)
  have n3 := index_ne w hn 1028 770 (by omega) (by omega) (by omega)
  have post : GatePhysical [.X (w 0),.CX (w 1028) (w 0),.CX (w 770) (w 1028)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,n1,n2]
  have mid : GatePhysical [.CX (w 1028) (w 770)] := by simp [GatePhysical,PhysicalInstr,ProperGate,n3]
  simp only [inverse,inverseUnmiddle,inverseBack,gatePhysical_append]
  exact ⟨⟨⟨ka,ro,mid⟩,hr⟩,cp,post⟩

end ECDSAAdd.Arithmetic.NativeFirstKnown
