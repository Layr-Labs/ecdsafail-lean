import ECDSAAdd.Arithmetic.Divsteps.PrepareControls
import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Whole-word activity tagging is self-inverse with clean detector workspace,
even though its measured AND work uses independent outcome lists. -/
theorem activityTag_after (one active : Wire) (bs : List ZeroBit)
    (hn : (one::active::bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (mf mi : List Bool) (ho : s.basis one=false)
    (hz : ∀ b∈bs,s.basis b.work=false) :
    run (activityTag one active bs) mi (run (activityTag one active bs) mf s)=s := by
  let t := run (activityTag one active bs) mf s
  have ht := activityTag_correct one active bs hn s mf ho hz
  have hoa : one≠active := by intro h; subst active; simp at hn
  have haway (b : ZeroBit) (hb : b∈bs) : b.input≠active ∧ b.work≠active := by
    have ha := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
    constructor <;> intro he <;> apply ha
    all_goals exact List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires,he]⟩
  have hot : t.basis one=false := by simpa [t,ht,writeBit,hoa] using ho
  have hzt : ∀ b∈bs,t.basis b.work=false := by
    intro b hb
    simpa [t,ht,writeBit,(haway b hb).2] using hz b hb
  have hinput : regValue (bs.map ZeroBit.input) t.basis=regValue (bs.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    simp [t,ht,writeBit,(haway b hb).1]
  have htwo := activityTag_correct one active bs hn t mi hot hzt
  rw [hinput] at htwo
  rw [htwo]
  dsimp only [t]
  rw [ht]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=active
  · subst w
    simp [writeBit]
  · simp [writeBit,hw]

/-- Only the gate-only branch tagger is reversed. The measured activity
circuit is uncomputed constructively using its own proved XOR semantics. -/
def inversePrepareControls (one active zsign glow parity swap : Wire) (bs : List ZeroBit) : Program :=
  (branchTags zsign glow parity swap).reverse ++ activityTag one active bs

theorem inversePrepareControls_after (one active zsign glow parity swap : Wire)
    (bs : List ZeroBit)
    (hn : (one::active::bs.flatMap ZeroBit.wires).Nodup)
    (hc : [zsign,glow,parity,swap].Nodup)
    (s : State) (mf mi : List Bool) (ho : s.basis one=false)
    (hz : ∀ b∈bs,s.basis b.work=false) :
    run (inversePrepareControls one active zsign glow parity swap bs) mi
      (run (prepareControls one active zsign glow parity swap bs) mf s)=s := by
  have hp : ProperProgram (branchTags zsign glow parity swap) := by
    simp only [ProperProgram,branchTags,List.mem_cons,List.not_mem_nil,or_false]
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl <;> simp_all [ProperGate]
  have hm : measurementCount (branchTags zsign glow parity swap).reverse=0 := by
    rw [measurementCount_reverse]
    exact (branchTags_resources zsign glow parity swap).2.1
  simp only [inversePrepareControls,prepareControls,run_append,run_take,hm,List.drop_zero]
  rw [run_reverse_proper _ hp]
  exact activityTag_after one active bs hn s mf mi ho hz

theorem inversePrepareControls_counts (one active zsign glow parity swap : Wire) (bs : List ZeroBit) :
    toffoliCount (inversePrepareControls one active zsign glow parity swap bs)=bs.length+1 ∧
    measurementCount (inversePrepareControls one active zsign glow parity swap bs)=bs.length := by
  simp [inversePrepareControls,toffoliCount_append,measurementCount_append,
    toffoliCount_reverse,measurementCount_reverse,
    (branchTags_resources zsign glow parity swap).1,(branchTags_resources zsign glow parity swap).2.1,
    (activityTag_counts one active bs).1,(activityTag_counts one active bs).2,Nat.add_comm]

end ECDSAAdd.Arithmetic.Divsteps
