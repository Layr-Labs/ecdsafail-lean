import ECDSAAdd.Arithmetic.Paper935.DecoderUnpad
import ECDSAAdd.Arithmetic.Paper935.CleanBranch

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps ECDSAAdd.Arithmetic.Divsteps

/-- Sign-extend physical rows, run the concrete five-depth branch decoder,
then restore the original windows. Only the proper padding is reversed. -/
def paddedCleanBranch (padding : Program) (layouts : List DepthLayout) (p : Int)
    (frozen fire active second sigma port : Wire) (rb : List ZeroBit) (k : Nat) : Program :=
  padding++(cleanBranchProgram layouts p frozen fire active second sigma port rb k++padding.reverse)

theorem paddedCleanBranch_run (p : Int) (st : ZState) (hi : Inv p st) (hp : p%2=1)
    (a b c d e : DepthLayout) (ha : a.low.length=2) (hb : b.low.length=3)
    (hc : c.low.length=4) (hd : d.low.length=5) (he : e.low.length=6)
    (frozen fire active sigma port : Wire) (fv : StepRow) (rb : List ZeroBit) (k r : Nat)
    (hn : [frozen,fire,active,fv.second,sigma,port].Nodup)
    (hr : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length) (hlt : r<k)
    (hport : port∉wires (clearHistoryControls frozen fire active fv.second sigma rb k))
    (oldFrozen armed : Bool) (hfg : oldFrozen=true → st.g=0)
    (hfirst : oldFrozen=false → armed=true → (zStep st).g=0 → st.g≠0)
    (padding : Program) (proper : ProperProgram padding) (away : port∉wires padding)
    (s : State) (m : List Bool) (hwork : ∀ b∈rb,(run padding m s).basis b.work=false)
    (hfire0 : (run padding m s).basis fire=false) (hactive : (run padding m s).basis active=false) (hsigma0 : (run padding m s).basis sigma=false)
    (hfrozen : (run padding m s).basis frozen=(oldFrozen || (!oldFrozen && armed && decide ((zStep st).g=0))))
    (hrecord : regValue (rb.map ZeroBit.input) (run padding m s).basis=
      (if !oldFrozen && armed && decide ((zStep st).g=0) then k else r))
    (hrow : signedRegValue fv.wires (run padding m s).basis=(if oldFrozen then st else zStep st).fv)
    (hready : ∀ L∈[a,b,c,d,e],L.Available st
      (run (mintHistoryControls frozen fire active fv.second sigma rb k) m (run padding m s)))
    (hout : ∀ L∈[a,b,c,d,e],L.output=port)
    (hfr : ∀ L∈[a,b,c,d,e],L.frozen.input=frozen) :
    let stored := !(oldFrozen || (!oldFrozen && armed && decide ((zStep st).g=0))) &&
      decide ((zStep st).z≤0) && decide ((2:Int)^7 ∣ (zStep st).fv)
    run (paddedCleanBranch padding [a,b,c,d,e] p frozen fire active fv.second sigma port rb k) m s=
      ⟨s.phase,writeBit s.basis port (s.basis port ^^ (!stored && decide (bbit st=1)))⟩ := by
  have decoded := cleanBranchProgram_run p st hi hp a b c d e ha hb hc hd he
    frozen fire active sigma port fv rb k r hn hr hk hlt hport oldFrozen armed hfg hfirst
    (run padding m s) m hwork hfire0 hactive hsigma0 hfrozen hrecord hrow hready hout hfr
  have count := properProgram_measurementCount padding proper
  dsimp only at decoded ⊢
  rw [paddedCleanBranch,run_append,run_take,count,List.drop_zero,run_append,run_take,decoded]
  rw [decoder_unpad padding proper port away s m]
  rw [FiniteUnitary.run_phase padding proper,run_preserves_outside padding m s port away]

theorem paddedCleanBranch_cancel (p : Int) (st : ZState) (hi : Inv p st) (hp : p%2=1)
    (a b c d e : DepthLayout) (ha : a.low.length=2) (hb : b.low.length=3)
    (hc : c.low.length=4) (hd : d.low.length=5) (he : e.low.length=6)
    (frozen fire active sigma port : Wire) (fv : StepRow) (rb : List ZeroBit) (k r : Nat)
    (hn : [frozen,fire,active,fv.second,sigma,port].Nodup)
    (hr : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length) (hlt : r<k)
    (hport : port∉wires (clearHistoryControls frozen fire active fv.second sigma rb k))
    (oldFrozen armed : Bool) (hfg : oldFrozen=true → st.g=0)
    (hfirst : oldFrozen=false → armed=true → (zStep st).g=0 → st.g≠0)
    (padding : Program) (proper : ProperProgram padding) (away : port∉wires padding)
    (s : State) (m : List Bool) (ordinal cursor : Nat) (hwork : ∀ b∈rb,(run padding (m.drop cursor) s).basis b.work=false)
    (hfire0 : (run padding (m.drop cursor) s).basis fire=false) (hactive : (run padding (m.drop cursor) s).basis active=false) (hsigma0 : (run padding (m.drop cursor) s).basis sigma=false)
    (hfrozen : (run padding (m.drop cursor) s).basis frozen=(oldFrozen || (!oldFrozen && armed && decide ((zStep st).g=0))))
    (hrecord : regValue (rb.map ZeroBit.input) (run padding (m.drop cursor) s).basis=
      (if !oldFrozen && armed && decide ((zStep st).g=0) then k else r))
    (hrow : signedRegValue fv.wires (run padding (m.drop cursor) s).basis=(if oldFrozen then st else zStep st).fv)
    (hready : ∀ L∈[a,b,c,d,e],L.Available st
      (run (mintHistoryControls frozen fire active fv.second sigma rb k) (m.drop cursor) (run padding (m.drop cursor) s)))
    (hout : ∀ L∈[a,b,c,d,e],L.output=port)
    (hfr : ∀ L∈[a,b,c,d,e],L.frozen.input=frozen)
    (hzero : s.basis port=false) (phase : Bool)
    (hphase : s.phase=(phase ^^ (m.getD ordinal false &&
      (!(!(oldFrozen || (!oldFrozen && armed && decide ((zStep st).g=0))) &&
        decide ((zStep st).z≤0) && decide ((2:Int)^7 ∣ (zStep st).fv)) && decide (bbit st=1))))) :
    let stored := !(oldFrozen || (!oldFrozen && armed && decide ((zStep st).g=0))) &&
      decide ((zStep st).z≤0) && decide ((2:Int)^7 ∣ (zStep st).fv)
    runWithTape (recoverBranch (paddedCleanBranch padding [a,b,c,d,e] p frozen fire active fv.second sigma port rb k)
      port ordinal) m cursor s=⟨phase,writeBit s.basis port (!stored && decide (bbit st=1))⟩ := by
  apply recoverBranch_cancel _ _ _ _ _ _ _ _ hphase
  simpa only [hzero,Bool.false_xor] using
    paddedCleanBranch_run p st hi hp a b c d e ha hb hc hd he frozen fire active sigma port fv rb k r hn hr hk hlt
      hport oldFrozen armed hfg hfirst padding proper away s (m.drop cursor) hwork hfire0 hactive hsigma0 hfrozen hrecord hrow hready hout hfr


end ECDSAAdd.Arithmetic.Paper935
