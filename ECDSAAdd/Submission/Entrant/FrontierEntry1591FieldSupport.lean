import ECDSAAdd.Submission.Entrant.FrontierEntry1591Selected

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierReplay1591
open Arithmetic MappedCompressed
attribute [local irreducible] wires

theorem packet_support_eq (divide : Bool) (j : Nat) :
    wires (packet divide j)=wires (OneFlagReplay.packet divide j) := by
  simp only [packet,OneFlagReplay.packet,renameProgram_support,basePacket,
    OneFlagReplay.basePacket,wires_append,NewHistory5.encode_support_eq,NewHistory5.decode_support_eq]
  rfl

theorem first_support_eq (divide : Bool) :
    wires (firstPacket divide)=wires (OneFlagReplay.firstPacket divide) := by
  simp only [firstPacket,OneFlagReplay.firstPacket,renameProgram_support,baseFirstPacket,
    OneFlagReplay.baseFirstPacket,wires_append,NewHistory5.encode_support_eq,NewHistory5.decode_support_eq]
  rfl

theorem groups_support_eq (divide : Bool) (j n : Nat) :
    wires (groups divide j n)=wires (OneFlagReplay.groups divide j n) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases divide <;> simp only [groups,OneFlagReplay.groups,PacketSequence.program,
      Bool.false_eq_true,if_false,if_true,wires_append]
    · rw [←OneFlagReplay.groups,←groups,ih,packet_support_eq]
    · rw [←OneFlagReplay.groups,←groups,ih,packet_support_eq]

theorem support_eq (divide : Bool) :
    wires (replay divide)=wires (OneFlagReplay.replay divide) := by
  have last : endPacket divide=OneFlagReplay.endPacket divide := rfl
  cases divide <;> simp only [replay,OneFlagReplay.replay,renameProgram_support,
    logicalReplay,OneFlagReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,first_support_eq,groups_support_eq,last]
end ECDSAAdd.Entrant.FrontierReplay1591

namespace ECDSAAdd.Entrant.FrontierSW1591
open Arithmetic MappedCompressed
attribute [local irreducible] wires

theorem packet_support_eq (divide : Bool) (j : Nat) :
    wires (packetS divide j)=wires (OneFlagSW.packetS divide j) := by
  simp only [packetS,OneFlagSW.packetS,renameProgram_support,basePacketS,
    OneFlagSW.basePacketS,wires_append,NewHistory5.encode_support_eq,NewHistory5.decode_support_eq]
  rfl

theorem first_support_eq (divide : Bool) :
    wires (firstPacketS divide)=wires (OneFlagSW.firstPacketS divide) := by
  simp only [firstPacketS,OneFlagSW.firstPacketS,renameProgram_support,baseFirstPacketS,
    OneFlagSW.baseFirstPacketS,wires_append,NewHistory5.encode_support_eq,NewHistory5.decode_support_eq]
  rfl

theorem groups_support_eq (divide : Bool) (j n : Nat) :
    wires (groupsS divide j n)=wires (OneFlagSW.groupsS divide j n) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases divide <;> simp only [groupsS,OneFlagSW.groupsS,PacketSequence.program,
      Bool.false_eq_true,if_false,if_true,wires_append]
    · rw [←OneFlagSW.groupsS,←groupsS,ih,packet_support_eq]
    · rw [←OneFlagSW.groupsS,←groupsS,ih,packet_support_eq]

theorem support_eq (divide : Bool) :
    wires (replayS divide)=wires (OneFlagSW.replayS divide) := by
  have last : endPacketS divide=OneFlagSW.endPacketS divide := rfl
  cases divide <;> simp only [replayS,OneFlagSW.replayS,renameProgram_support,
    logicalReplayS,OneFlagSW.logicalReplayS,Bool.false_eq_true,if_false,if_true,
    wires_append,first_support_eq,groups_support_eq,last]
end ECDSAAdd.Entrant.FrontierSW1591

namespace ECDSAAdd.Entrant.FrontierFieldSupport1591
open Arithmetic MappedCompressed OneFlagReplay
attribute [local irreducible] wires

def host : Wire := base 1543

private theorem no_append (q : Wire) (P Q : Program)
    (hp : q∉wires P) (hq : q∉wires Q) : q∉wires (P++Q) := by
  simpa only [wires_append,Finset.mem_union,not_or] using And.intro hp hq

private theorem no_rename (f : Wire → Wire) (hf : Function.Injective f)
    (a b : Wire) (P : Program) (fix : f a=b) (hp : a∉wires P) :
    b∉wires (renameProgram f P) := by
  intro used
  rw [renameProgram_support] at used
  obtain ⟨old,mem,eq⟩ := Finset.mem_image.mp used
  exact hp (hf (eq.trans fix.symm) ▸ mem)

private theorem codec_free (start : Nat) (hs : start+5≤510) (P : Program)
    (hp : P=History5.encode base start ∨ P=History5.decode base start) :
    base 1538∉wires P := by
  intro used
  obtain ⟨r,eq⟩ := History5.history_gate_mem base start P hp _ used
  have same := base_injective eq
  have hr := r.isLt
  unfold History5.historyMap History5.historyId at same
  split_ifs at same <;> omega

private theorem field_free : base 1538∉fieldSites := by
  intro used
  rcases List.mem_cons.mp (List.mem_toFinset.mp used) with eq | used
  · have same := base_injective eq; omega
  · obtain ⟨i,hi,eq⟩ := List.mem_map.mp used
    have same := base_injective eq
    simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false] at hi
    omega

private theorem read_free (j : Nat) (hj : j<102) : base 1538∉readSites (5*j) := by
  intro used
  simp only [readSites,Finset.mem_union] at used
  rcases used with (used | used) | used
  · exact field_free used
  · simp only [Finset.mem_insert,Finset.mem_singleton] at used
    rcases used with eq | eq <;> have same := base_injective eq <;> omega
  · exact codec_free (5*j) (by omega) _ (Or.inl rfl) used

private theorem pi_fix (j : Nat) (hj : j<102) :
    shifted (Placement5.pi j) (base 1538)=base 1538 := by
  rw [shifted_base,Placement5.pi_outside j 1538 hj]
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
  omega

private theorem packet_free (divide : Bool) (j : Nat) (hj : j<102) :
    base 1538∉wires (packet divide j) := by
  apply no_rename _ (shifted (Placement5.pi j)).injective _ _ _ (pi_fix j hj)
  apply no_append
  · apply no_append
    · exact codec_free _ (by omega) _ (Or.inr rfl)
    · exact fun used => read_free j hj (body_support divide j hj used)
  · exact codec_free _ (by omega) _ (Or.inl rfl)

private theorem first_free (divide : Bool) : base 1538∉wires (firstPacket divide) := by
  apply no_rename _ (shifted (Placement5.pi 0)).injective _ _ _ (pi_fix 0 (by omega))
  apply no_append
  · apply no_append
    · exact codec_free 0 (by omega) _ (Or.inr rfl)
    · exact fun used => read_free 0 (by omega) (firstBody_support divide used)
  · exact codec_free 0 (by omega) _ (Or.inl rfl)

private theorem end_free (divide : Bool) : base 1538∉wires (endPacket divide) := by
  have fix : shifted Placement5.pi0 (base 1538)=base 1538 := by
    rw [shifted_base,Placement5.pi0_outside]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
    omega
  apply no_rename _ (shifted Placement5.pi0).injective _ _ _ fix
  intro used
  rcases Finset.mem_union.mp (rawEnd_support divide used) with h | h
  · exact field_free h
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with eq | eq <;> have same := base_injective eq <;> omega

private theorem groups_free (divide : Bool) (j n : Nat) (hn : j+n≤102) :
    base 1538∉wires (groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,wires]
  | succ n ih =>
    have head := packet_free divide j (by omega)
    have tail := ih (j+1) (by omega)
    cases divide
    · exact no_append _ _ _ tail head
    · exact no_append _ _ _ head tail

private theorem old_replay_free (divide : Bool) : host∉wires (replay divide) := by
  have logical : base 1538∉wires (logicalReplay divide) := by
    have first := first_free divide
    have mid := groups_free divide 1 101 (by omega)
    have last := end_free divide
    cases divide
    · exact no_append _ _ _ (no_append _ _ _ last mid) first
    · exact no_append _ _ _ (no_append _ _ _ first mid) last
  exact no_rename _ (OB5.sig_injective 511 (by omega)) _ _ _ (by decide +kernel) logical

theorem replay_avoids (divide : Bool) : host∉wires (FrontierSW1591.replayS divide) := by
  rw [FrontierSW1591.support_eq]
  exact fun used => old_replay_free divide ((OneFlagSW.selReplay_sel divide).sub.wires_sub used)

private theorem old_endpoint_free (P : Program)
    (hp : wires P⊆(HalfField.ids.map base).toFinset) : base 1538∉wires P := by
  intro used
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp (hp used))
  have same := base_injective eq
  simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hi
  omega

private theorem endpoint_host : HalfFieldOB5.endpointMap (base 1538)=host := by
  change OB5.sig 511 (Equiv.swap (base 1796) (base 1285)
    (shifted (Placement5.pi 51) (shifted HalfFieldOB5.bank (base 1538))))=host
  have bank : HalfFieldOB5.bank 1538=1538 := by decide +kernel
  rw [shifted_base,bank,shifted_base,
    Placement5.pi_outside 51 1538 (by omega) (by
      unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      omega)]
  decide +kernel

theorem endpoints_avoid : host∉wires OwnQ5Endpoint.centerT ∧ host∉wires OwnQ5Endpoint.canonT := by
  have center := no_rename _ HalfFieldOB5.endpointMap.injective _ _ _ endpoint_host
    (old_endpoint_free _ HalfField.centerT_sites)
  have canon := no_rename _ HalfFieldOB5.endpointMap.injective _ _ _ endpoint_host
    (old_endpoint_free _ HalfField.canonT_sites)
  have step (e : Equiv.Perm Wire) (P : Program) (fix : e host=host) (hp : host∉wires P) :
      host∉wires (renameProgram e P) := no_rename e e.injective _ _ _ fix hp
  exact ⟨step OwnQ5Endpoint.swap _ (by decide +kernel)
      (step OwnQ4Endpoint.swap _ (by decide +kernel)
        (step OwnGuardEndpoint.swap _ (by decide +kernel)
          (step OwnPlusEndpoint.swap _ (by decide +kernel) center))),
    step OwnQ5Endpoint.swap _ (by decide +kernel)
      (step OwnQ4Endpoint.swap _ (by decide +kernel)
        (step OwnGuardEndpoint.swap _ (by decide +kernel)
          (step OwnPlusEndpoint.swap _ (by decide +kernel) canon)))⟩

theorem copy_avoids : host∉wires HalfFieldOB5.copyN := by
  intro used
  have mem := copyRegister_wires_subset none
    (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y used
  simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append,
    balancedSharedPorts_r,balancedSharedPorts_y] at mem
  rcases mem with r | y
  · exact OwnPlusHost.not_block 1543 2056 256 (by omega) r
  · exact OwnPlusHost.not_block 1543 770 256 (by omega) y

theorem segment_avoids (divide : Bool) : host∉wires (FrontierSW1591.segmentS divide) := by
  have ends := endpoints_avoid
  have replay := replay_avoids divide
  cases divide
  · exact no_append _ _ _ ends.1 (no_append _ _ _ copy_avoids (no_append _ _ _ replay ends.2))
  · exact no_append _ _ _ ends.1 (no_append _ _ _ replay (no_append _ _ _ copy_avoids ends.2))

theorem hosted_avoids (P : Program) (hp : host∉wires P) :
    host∉wires ([Instr.X (base 511)]++(renameProgram HostOB5.hostSwap P++[Instr.X (base 511)])) := by
  have x : host∉wires [Instr.X (base 511)] := by simp [host,wires,Instr.wires,base]
  exact no_append _ _ _ x (no_append _ _ _
    (no_rename _ HostOB5.hostSwap_injective _ _ _ (by decide +kernel) hp) x)

end ECDSAAdd.Entrant.FrontierFieldSupport1591
