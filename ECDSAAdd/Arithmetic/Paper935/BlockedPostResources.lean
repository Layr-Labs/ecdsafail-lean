import ECDSAAdd.Arithmetic.Paper935.BlockedPostInverse

namespace ECDSAAdd.Arithmetic.Paper935.BlockedPost
open ECDSAAdd.Arithmetic.Paper935

theorem inverse_counts (armed : Bool) (one zf frozen fire active : Wire)
    (bs : List BlockedZero.Block) (rb : List ZeroBit) (k : Nat) :
    toffoliCount (publicPostInverse armed one zf frozen fire active bs rb k)=
      (if armed then 4*(BlockedZero.inputs bs).length+1+rb.length else 0) ∧
    measurementCount (publicPostInverse armed one zf frozen fire active bs rb k)=
      (if armed then 4*(BlockedZero.inputs bs).length+rb.length else 0) := by
  have hp := BlockedZero.counts one zf bs
  have hl := freezeLatch_counts zf frozen fire (rb.map ZeroBit.input) k
  have hc := equalConstant_counts frozen fire rb k
  cases armed <;>
    simp [publicPostInverse,zeroFreezeInverse,zeroLatchInverse,latchRetireInverse,
      toffoliCount_append,measurementCount_append,
      hp.1,hp.2,hl.2.2.1,hl.2.2.2,hc.1,hc.2,retireActivity,toffoliCount,measurementCount]; omega

theorem inverse_support (armed : Bool) (one zf frozen fire active witness : Wire)
    (bs : List BlockedZero.Block) (rb : List ZeroBit) (k : Nat) :
    wires (publicPostInverse armed one zf frozen fire active bs rb k) ⊆
      (one::zf::frozen::fire::active::witness::
        (rb.map ZeroBit.input++BlockedZero.ports bs++rb.flatMap ZeroBit.wires)).toFinset := by
  let W := (one::zf::frozen::fire::active::witness::
        (rb.map ZeroBit.input++BlockedZero.ports bs++rb.flatMap ZeroBit.wires)).toFinset
  have hp : wires (BlockedZero.program one zf bs) ⊆ W :=
    (BlockedZero.support one zf bs).trans (by intro q hq; simp only [W,List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto)
  have hl : wires (freezeUnlatch zf frozen fire (rb.map ZeroBit.input) k) ⊆ W :=
    (freezeLatch_support zf frozen fire (rb.map ZeroBit.input) k).2.trans
      (by intro q hq; simp only [W,List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto)
  have ha : wires (retireActivity frozen fire active).reverse ⊆ W := by
    rw [wires_reverse,(activity_wires frozen fire active).2]
    intro q hq
    simp only [W,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hc : wires (equalConstant frozen fire rb k) ⊆ W := by
    rw [equalConstant_wires]
    intro q hq
    simp only [W,List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    tauto
  cases armed
  · exact ha
  · change wires (equalConstant frozen fire rb k ++
      (BlockedZero.program one zf bs ++
        (((retireActivity frozen fire active).reverse ++ freezeUnlatch zf frozen fire (rb.map ZeroBit.input) k) ++
          BlockedZero.program one zf bs))) ⊆ W
    simp only [wires_append]
    exact Finset.union_subset hc (Finset.union_subset hp (Finset.union_subset (Finset.union_subset ha hl) hp))

end ECDSAAdd.Arithmetic.Paper935.BlockedPost
