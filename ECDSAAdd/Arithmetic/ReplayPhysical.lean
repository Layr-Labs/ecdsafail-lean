import ECDSAAdd.Arithmetic.ControlledUnaryPhysical
import ECDSAAdd.Arithmetic.ModularPhysical
import ECDSAAdd.Arithmetic.ReplayLoop

namespace ECDSAAdd.Arithmetic

theorem replayCells_physical (a s t : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hn : ([a,s,t]++L.wires).Nodup) (hpos : 0<n) :
    GatePhysical (replayCell a s t L p) ∧ GatePhysical (replayUncell a s t L p) := by
  have ctl (c : Wire) (hc : c ∈ [a,s,t]) : (c::L.wires).Nodup := by
    have h := List.nodup_append'.mp hn
    exact List.nodup_cons.mpr ⟨List.disjoint_left.mp h.2.2 hc,h.2.1⟩
  have ht := ctl t (by simp)
  have ha := ctl a (by simp)
  have hs := ctl s (by simp)
  have ns : (s::L.z.take L.low.length++L.a.take L.low.length).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have H := List.nodup_iff_count.mp hs q
    have hz := (List.take_sublist L.low.length L.z).count_le q
    have hz' := (List.take_sublist L.low.length L.a).count_le q
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at H ⊢
    omega
  have nu : (a::L.unary.wires).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have H := List.nodup_iff_count.mp ha q
    simp only [ModInPlaceLayout.unary,ModInPlaceLayout.wires,ModInPlaceLayout.work,
      ModInPlaceLayout.z,ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.z,
      ModUnaryLayout.core,ModAddCoreLayout.work,ModAddCoreLayout.z,
      List.count_append,List.count_cons,List.count_nil] at H ⊢
    omega
  have sw := swapRegisters_physical s _ _ ns
  have un := controlledUnary_physical a L.unary n p (L.unary_widths n hw) nu hpos
  have add := controlledModAdd_physical t L p ht
  have sub := controlledModSub_physical t L p ht
  simp only [replayCell,replayUncell,gatePhysical_append]
  exact ⟨⟨⟨⟨sw,sub⟩,un.1⟩,sw⟩,⟨⟨⟨sw,un.2⟩,add⟩,sw⟩⟩

theorem replayLoops_physical (L : ReplayLayout) (rs : List RoundRecord) (n p i : Nat)
    (hv : L.Valid n rs) (hpos : 0<n) :
    GatePhysical (replayLoop L p i rs) ∧ GatePhysical (replayUnloop L p i rs) := by
  induction rs generalizing i with
  | nil => simp [replayLoop,replayUnloop,GatePhysical]
  | cons r rs ih =>
    have ac := counterActiveXor_physical L.counter L.active i hv.counterNodup
    have cell := replayCells_physical L.active r.swap r.subtract L.payload n p
      hv.widths (hv.cell L n (r::rs) r (by simp)) hpos
    have ht := ih (i+1) (hv.tail L n r rs)
    simp only [replayLoop,replayUnloop,replayRound,replayUnround,gatePhysical_append]
    exact ⟨⟨⟨⟨ac,cell.1⟩,ac⟩,ht.1⟩,⟨ht.2,⟨⟨ac,cell.2⟩,ac⟩⟩⟩

end ECDSAAdd.Arithmetic
