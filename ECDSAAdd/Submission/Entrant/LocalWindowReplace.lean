import ECDSAAdd.Submission.Entrant.MainPart07

namespace ECDSAAdd.Entrant.LocalWindowReplace
open ECDSAAdd Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run wires

theorem after_forward (P Q F : Program) (sites : List Wire)
    (hp : wires P⊆sites.toFinset) (hq : wires Q⊆sites.toFinset) (hf : wires F⊆sites.toFinset)
    (a state : State) (pre : BasisState)
    (reads : ∀q∈sites,a.basis q=pre q)
    (agree : ∀q∈sites,state.basis q=(run F [] a).basis q)
    (m n : List Bool)
    (law : run P m ⟨false,(run F [] ⟨false,pre⟩).basis⟩=
      run Q n ⟨false,(run F [] ⟨false,pre⟩).basis⟩) : run P m state=run Q n state := by
  apply Stack5.local_replace P Q sites.toFinset hp hq state
    ⟨false,(run F [] ⟨false,pre⟩).basis⟩ m n
  · intro q hmem
    have member := List.mem_toFinset.mp hmem
    exact (agree q member).trans (site_run F sites hf a ⟨false,pre⟩ reads [] q member)
  · exact law

end ECDSAAdd.Entrant.LocalWindowReplace
