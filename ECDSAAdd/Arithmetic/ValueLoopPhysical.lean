import ECDSAAdd.Arithmetic.ValueRoundPhysical
import ECDSAAdd.Arithmetic.ValueLoopResources

namespace ECDSAAdd.Arithmetic

theorem valueLoops_physical (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat)
    (hn : (L.tapeWires rs).Nodup) (hd : 2 ≤ L.data.width) :
    GatePhysical (valueLoop L i rs) ∧ GatePhysical (valueUnloop L i rs) := by
  induction rs generalizing L i with
  | nil => simp [valueLoop,valueUnloop,GatePhysical]
  | cons r rs ih =>
    have hb := valueWidth_bounds L.data.width i hd
    have hW := L.withRecord_nodup r rs hn
    have hN := ((L.withRecord r).narrow_nodup _ (by omega) hb.2 hW).1
    have hr := valueRounds_physical ((L.withRecord r).narrow (valueWidth L.data.width i)) hN i
    have ht := ih L.swapCounter (i+1) (L.tail_nodup r rs hn) hd
    simp only [valueLoop,valueUnloop,gatePhysical_append]
    exact ⟨⟨hr.1,ht.1⟩,⟨ht.2,hr.2⟩⟩

end ECDSAAdd.Arithmetic
