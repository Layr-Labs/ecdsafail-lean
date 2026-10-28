import ECDSAAdd.Arithmetic.Paper935.WindowRowsLocality

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

private theorem rowStage_in_set (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
    (S : Finset Wire)
    (h1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).toFinset⊆S)
    (h2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).toFinset⊆S)
    (h3 : (active::vlow::(vmid++[vsign])).toFinset⊆S) :
    wires (rowStage q parity u k active glow gsign vlow vsign f gmid vmid gv)⊆S := by
  rw [rowStage,wires_append]
  apply Finset.union_subset
  · rw [branchPair,wires_append]
    exact Finset.union_subset ((branchRow_support q parity u k f (glow::(gmid++[gsign]))).trans h1)
      ((branchRow_support q parity u k (vlow::(vmid++[vsign])) gv).trans h2)
  · rw [finishRows,wires_append,doubleSigned_wires,skywalkSignedHalf_wires]
    apply Finset.union_subset h3
    intro w hw
    apply h1
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl <;> simp

private theorem routedStage_in_set (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
    (hf : f.length=gmid.length+2) (hv : gv.length=vmid.length+2)
    (S : Finset Wire)
    (h1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).toFinset⊆S)
    (h2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).toFinset⊆S)
    (h3 : (active::vlow::(vmid++[vsign])).toFinset⊆S) :
    wires (routedStage q parity u k active glow gsign vlow vsign f gmid vmid gv)⊆S := by
  rw [routedStage,wires_append]
  apply Finset.union_subset
  · intro w hw
    have hh := swapRegisters_wires q (f++(vlow::(vmid++[vsign])))
      ((glow::(gmid++[gsign]))++gv) (by simp [hf,hv]; omega) hw
    have hm : w∈(q::parity::u::k::(f++(glow::(gmid++[gsign])))).toFinset ∨
        w∈(q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).toFinset := by
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
      tauto
    exact hm.elim (fun h => h1 h) (fun h => h2 h)
  · exact rowStage_in_set q parity u k active glow gsign vlow vsign f gmid vmid gv S h1 h2 h3

/-- Exact routed support includes only its five controls and actual row sites. -/
theorem RoutedBankLayout.program_support (L : RoutedBankLayout) (valid : L.Valid) :
    wires L.program⊆([L.q,L.parity,L.u,L.k,L.active]++L.before.rows.flatMap WindowRow.wires).toFinset := by
  apply routedStage_in_set L.q L.parity L.u L.k L.active L.glow L.gsign L.vlow L.vsign
    L.f.wires L.gmid L.vmid L.gv.wires valid.fgLength valid.vLength
  all_goals
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,RoutedBankLayout.before,WindowBank.rows,
      WindowRow.wires,List.flatMap_cons,List.flatMap_nil,List.not_mem_nil,or_false] at hq ⊢
    clear valid
    tauto

end ECDSAAdd.Arithmetic.Paper935
