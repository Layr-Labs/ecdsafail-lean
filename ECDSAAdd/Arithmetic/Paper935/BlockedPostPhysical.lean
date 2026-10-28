import ECDSAAdd.Arithmetic.Paper935.BlockedPostResources

namespace ECDSAAdd.Arithmetic.Paper935.BlockedPost
open ECDSAAdd.Arithmetic.Paper935 RecordedQuantum

private theorem latch_physical (zf frozen fire active : Wire) (record : List Wire) (k : Nat)
    (hn : [zf,frozen,fire,active].Nodup) (hf : fire∉record) :
    GatePhysical (latchRetireActivity zf frozen fire active record k) ∧
    GatePhysical (latchRetireInverse zf frozen fire active record k) := by
  have hc := maskedConstant_physical fire record k hf
  have hm : GatePhysical (mintFire zf frozen fire) := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    simp [mintFire,GatePhysical,PhysicalInstr,ProperGate]; tauto
  have hr : GatePhysical (recordToggle fire frozen record k) := by
    rw [recordToggle,gatePhysical_append]
    refine ⟨?_,hc⟩
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    simp [GatePhysical,PhysicalInstr,ProperGate]; tauto
  have ha : GatePhysical (retireActivity frozen fire active) := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    simp [retireActivity,GatePhysical,PhysicalInstr,ProperGate]; tauto
  have har : GatePhysical (retireActivity frozen fire active).reverse := by
    simpa only [GatePhysical,List.mem_reverse] using ha
  simp only [latchRetireActivity,latchRetireInverse,freezeLatch,freezeUnlatch,gatePhysical_append]
  exact ⟨⟨⟨hm,hr⟩,ha⟩,har,hr,hm⟩

theorem post_physical (armed : Bool) (one zf frozen fire active witness : Wire)
    (bs : List BlockedZero.Block) (rb : List ZeroBit) (k : Nat)
    (hp : BlockedZero.Valid one zf bs) (hn : [zf,frozen,fire,active].Nodup)
    (hf : fire∉rb.map ZeroBit.input)
    (hc : (one::witness::rb.flatMap ZeroBit.wires).Nodup)
    (hi : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) :
    GatePhysical (publicPost armed one zf frozen fire active witness bs rb k) ∧
    GatePhysical (publicPostInverse armed one zf frozen fire active bs rb k) := by
  have hprobe := BlockedZero.physical one zf bs hp
  have hl := latch_physical zf frozen fire active (rb.map ZeroBit.input) k hn hf
  have hcompare := equalConstant_physical one witness rb k hc
  have hremint := equalConstant_physical frozen fire rb k hi
  have herase : GatePhysical (eraseAnd witness frozen fire) := by
    simp [eraseAnd,GatePhysical,PhysicalInstr]
  cases armed with
  | true =>
    simp only [publicPost,publicPostInverse,ite_true,zeroFreeze,zeroFreezeInverse,zeroLatch,
      zeroLatchInverse,fireCleanup,gatePhysical_append]
    exact ⟨⟨⟨hprobe,hl.1,hprobe⟩,⟨hcompare,herase⟩,hcompare⟩,
      hremint,hprobe,hl.2,hprobe⟩
  | false =>
    simp only [publicPost,publicPostInverse,Bool.false_eq_true,ite_false]
    have ha : GatePhysical (retireActivity frozen fire active) := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
      simp [retireActivity,GatePhysical,PhysicalInstr,ProperGate]; tauto
    exact ⟨ha,by simpa only [GatePhysical,List.mem_reverse] using ha⟩

end ECDSAAdd.Arithmetic.Paper935.BlockedPost
