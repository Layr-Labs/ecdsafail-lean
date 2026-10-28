import ECDSAAdd.Arithmetic.ValueLoopPhysical
import ECDSAAdd.Arithmetic.ReplayPhysical
import ECDSAAdd.Arithmetic.DialogLoad

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem safeDivisor_physical (g : Wire) (src : List Wire) (h : Wire) (t : List Wire)
    (hn : (g::src++(h::t)).Nodup) : GatePhysical (safeDivisor g src h t) := by
  have hg : g ∉ h::t := fun hm => (List.nodup_cons.mp hn).1 (List.mem_append_right _ hm)
  have gh : g ≠ h := fun he => hg (by simp [he])
  simp only [safeDivisor,gatePhysical_append]
  exact ⟨by simp [GatePhysical,PhysicalInstr,ProperGate,gh],
    copyRegister_physical (some g) src (h::t) hn.tail (by intro c hc; cases hc; exact hg)⟩

theorem dialogLoad_physical (L : DialogLayout) (p : Nat) (hn : L.wires.Nodup) :
    GatePhysical (dialogLoad L p) := by
  have hd := L.load_nodup hn
  unfold dialogLoad
  rw [gatePhysical_append]
  refine ⟨xorConstant_physical _ _,?_⟩
  cases he : L.first.low.map (·.v) with
  | nil => simp [GatePhysical]
  | cons h ts =>
    apply safeDivisor_physical
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hd w
    simp only [DialogLayout.vLow,he,List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega

theorem exchangeRegisters_physical (a b : List Wire) (hn : (a++b).Nodup) :
    GatePhysical (exchangeRegisters a b) := by
  have ha := copyRegister_physical none a b hn (by simp)
  have hb := copyRegister_physical none b a (List.nodup_append_comm.mpr hn) (by simp)
  simp only [exchangeRegisters,gatePhysical_append]
  exact ⟨⟨hb,ha⟩,hb⟩

theorem dialogs_physical (L : DialogLayout) (p : Nat) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (dialogDivide L p) ∧ GatePhysical (dialogMultiply L p) := by
  have hd : 2 ≤ L.first.data.width := by
    simp [KaliskiRoundLayout.data,RoundDataLayout.width,hw.low]
  have vl := valueLoops_physical L.first L.records 0 hn hd
  have rl := replayLoops_physical L.replay L.records 256 p 0 (L.replay_valid hw hn) (by decide)
  have load := dialogLoad_physical L p hn
  have nd : (L.y++L.z).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (L.registerWires_perm.nodup_iff.mpr hn) q
    simp only [DialogLayout.registerWires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have ex := exchangeRegisters_physical L.y L.z nd
  simp only [dialogDivide,dialogMultiply,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨load,vl.1⟩,ex⟩,rl.1⟩,vl.2⟩,load⟩,
    ⟨⟨⟨⟨⟨load,vl.1⟩,rl.2⟩,ex⟩,vl.2⟩,load⟩⟩

end ECDSAAdd.Arithmetic
