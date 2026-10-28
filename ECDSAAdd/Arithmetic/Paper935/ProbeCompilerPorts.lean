import ECDSAAdd.Arithmetic.Paper935.ProbeCompilerTotal

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileProbe_identity (one target : Wire) (inputs work : List Wire) (width : Nat)
    (bs : List BlockedZero.Block) (h : compileProbe one target inputs work width=some bs) :
    bs=BlockedZero.chunks (probeCandidate inputs work width).1 (probeCandidate inputs work width).2 := by
  unfold compileProbe at h
  dsimp only at h
  split at h
  next valid => cases h; rfl
  next invalid => simp at h

/-- Physical ports of the checked probe lie in its supplied inputs and pool. -/
theorem compileProbe_ports (one target : Wire) (inputs work : List Wire) (width : Nat)
    (bs : List BlockedZero.Block) (h : compileProbe one target inputs work width=some bs) :
    ∀ q∈BlockedZero.ports bs,q∈inputs++work := by
  have contract := compileProbe_contract one target inputs work width bs h
  have scratch := compileProbe_work one target inputs work width bs h
  intro q hq
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact List.mem_append_right _ (scratch.1 b hb)
  · obtain ⟨x,hx,hq⟩ := List.mem_flatMap.mp hq
    simp only [ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · apply List.mem_append_left
      rw [←contract.2]
      exact List.mem_flatMap.mpr ⟨b,hb,List.mem_map_of_mem hx⟩
    · exact List.mem_append_right _ (scratch.2 b hb x hx)

end ECDSAAdd.Arithmetic.Paper935
