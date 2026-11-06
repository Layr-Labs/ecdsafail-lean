import ECDSAAdd.Submission.Entrant.TerminalFiveSampleCore

namespace ECDSAAdd.Entrant.TerminalFiveSample
open ECDSAAdd Arithmetic MappedCompressed Challenge CompactCertificates
open TerminalFiveBridge
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run wires

theorem physical_support : wires physical ⊆ TerminalFiveDomain.sites.toFinset := by
  have table : ∀i∈Finset.range 40,perm i∈TerminalFiveDomain.sites := by decide +kernel
  intro q hq
  rw [physical,renameProgram_support] at hq
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
  exact List.mem_toFinset.mpr (table i (TerminalInverse23.support hi))

theorem old_support : wires TerminalFivePlacement.old ⊆ TerminalFiveDomain.sites.toFinset := by
  have contain : Inverse14Width.sites.toFinset ⊆ TerminalFiveDomain.sites.toFinset := by decide +kernel
  rw [TerminalFivePlacement.old,wires_append,Finset.union_subset_iff]
  exact ⟨Inverse14Width.support.trans contain,by decide +kernel⟩

theorem forward_support : wires forward ⊆ TerminalFiveDomain.sites.toFinset := by
  have contain : InverseFour15.sites15.toFinset ⊆ TerminalFiveDomain.sites.toFinset := by decide +kernel
  rw [forward,wires_append,Finset.union_subset_iff]
  exact ⟨by decide +kernel,InverseFour15.forward_support.trans contain⟩


end ECDSAAdd.Entrant.TerminalFiveSample
