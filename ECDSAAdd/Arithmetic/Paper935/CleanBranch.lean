import ECDSAAdd.Arithmetic.Paper935.HistoryControlValues
import ECDSAAdd.Arithmetic.Paper935.BranchRecovery

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps ECDSAAdd.Arithmetic.Divsteps

/-- Recompute the controls, decode the measured branch, and release the controls. -/
def cleanBranchProgram (layouts : List DepthLayout) (p : Int)
    (frozen fire active second sigma port : Wire) (rb : List ZeroBit) (k : Nat) : Program :=
  mintHistoryControls frozen fire active second sigma rb k ++
    (finiteBranchProgram layouts p sigma fire port ++
      clearHistoryControls frozen fire active second sigma rb k)

theorem cleanBranchProgram_run (p : Int) (st : ZState) (hi : Inv p st) (hp : p%2=1)
    (a b c d e : DepthLayout) (ha : a.low.length=2) (hb : b.low.length=3)
    (hc : c.low.length=4) (hd : d.low.length=5) (he : e.low.length=6)
    (frozen fire active sigma port : Wire) (fv : StepRow) (rb : List ZeroBit) (k r : Nat)
    (hn : [frozen,fire,active,fv.second,sigma,port].Nodup)
    (hr : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length) (hlt : r<k)
    (hport : port∉wires (clearHistoryControls frozen fire active fv.second sigma rb k))
    (oldFrozen armed : Bool) (hfg : oldFrozen=true → st.g=0)
    (hfirst : oldFrozen=false → armed=true → (zStep st).g=0 → st.g≠0)
    (s : State) (m : List Bool) (hwork : ∀ b∈rb,s.basis b.work=false)
    (hfire0 : s.basis fire=false) (hactive : s.basis active=false) (hsigma0 : s.basis sigma=false)
    (hfrozen : s.basis frozen=(oldFrozen || (!oldFrozen && armed && decide ((zStep st).g=0))))
    (hrecord : regValue (rb.map ZeroBit.input) s.basis=
      (if !oldFrozen && armed && decide ((zStep st).g=0) then k else r))
    (hrow : signedRegValue fv.wires s.basis=(if oldFrozen then st else zStep st).fv)
    (hready : ∀ L∈[a,b,c,d,e],L.Available st
      (run (mintHistoryControls frozen fire active fv.second sigma rb k) m s))
    (hout : ∀ L∈[a,b,c,d,e],L.output=port)
    (hfr : ∀ L∈[a,b,c,d,e],L.frozen.input=frozen) :
    let stored := !(oldFrozen || (!oldFrozen && armed && decide ((zStep st).g=0))) &&
      decide ((zStep st).z≤0) && decide ((2:Int)^7 ∣ (zStep st).fv)
    run (cleanBranchProgram [a,b,c,d,e] p frozen fire active fv.second sigma port rb k) m s=
      ⟨s.phase,writeBit s.basis port (s.basis port ^^ (!stored && decide (bbit st=1)))⟩ := by
  have hnc : [frozen,fire,active,fv.second,sigma].Nodup := by
    exact List.Nodup.of_append_left (l₂ := [port]) (by simpa only [List.cons_append,List.nil_append] using hn)
  have hfs : fire≠sigma := by simp_all
  have hnd : [sigma,fire,port].Nodup := by simp_all [hfs.symm]
  have hfa : fire≠active := by simp_all
  have hfrs : frozen≠sigma := by simp_all
  have hfra : frozen≠active := by simp_all
  have hfrf : frozen≠fire := by simp_all
  have hps : port≠sigma := Ne.symm (by simp_all : sigma≠port)
  have hpa : port≠active := Ne.symm (by simp_all : active≠port)
  have hpf : port≠fire := Ne.symm (by simp_all : fire≠port)
  let fired := !oldFrozen && armed && decide ((zStep st).g=0)
  let mint := mintHistoryControls frozen fire active fv.second sigma rb k
  let t := run mint m s
  have ht := historyControls_values p st hi hp frozen fire active sigma fv rb k r hnc hr hk hlt
    oldFrozen fired (by intro ho; simp [fired,ho]) s m hwork hfire0 hactive hsigma0 hfrozen hrecord hrow
  have tq : t.basis sigma=(!oldFrozen && decide (0≤st.z ∧ st.g%2=1)) := by rw [show t= _ from ht]; simp [writeBit]
  have tf : t.basis fire=fired := by rw [show t= _ from ht]; simp [writeBit,hfs,hfa]
  have tp : t.basis port=s.basis port := by rw [show t= _ from ht]; simp [writeBit,hps,hpa,hpf]
  have tfr : t.basis frozen=s.basis frozen := by rw [show t= _ from ht]; simp [writeBit,hfrs,hfra,hfrf]
  have decoded := finiteBranchProgram_run p st hi hp a b c d e ha hb hc hd he sigma fire port hnd
    oldFrozen armed hfg hfirst t (m.drop (measurementCount mint)) hready hout
    (by intro L hL; rw [hfr L hL,tfr,hfrozen]) tq tf
  rw [cleanBranchProgram,run_append,run_take,run_append,run_take,decoded]
  rw [historyControls_clear_after_write frozen fire active fv.second sigma port rb k hnc hr hk hport s m _ hwork]
  rw [tp,tf]

theorem cleanBranch_cancel (p : Int) (st : ZState) (hi : Inv p st) (hp : p%2=1)
    (a b c d e : DepthLayout) (ha : a.low.length=2) (hb : b.low.length=3)
    (hc : c.low.length=4) (hd : d.low.length=5) (he : e.low.length=6)
    (frozen fire active sigma port : Wire) (fv : StepRow) (rb : List ZeroBit) (k r : Nat)
    (hn : [frozen,fire,active,fv.second,sigma,port].Nodup)
    (hr : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length) (hlt : r<k)
    (hport : port∉wires (clearHistoryControls frozen fire active fv.second sigma rb k))
    (oldFrozen armed : Bool) (hfg : oldFrozen=true → st.g=0)
    (hfirst : oldFrozen=false → armed=true → (zStep st).g=0 → st.g≠0)
    (s : State) (m : List Bool) (ordinal cursor : Nat) (hwork : ∀ b∈rb,s.basis b.work=false)
    (hfire0 : s.basis fire=false) (hactive : s.basis active=false) (hsigma0 : s.basis sigma=false)
    (hfrozen : s.basis frozen=(oldFrozen || (!oldFrozen && armed && decide ((zStep st).g=0))))
    (hrecord : regValue (rb.map ZeroBit.input) s.basis=
      (if !oldFrozen && armed && decide ((zStep st).g=0) then k else r))
    (hrow : signedRegValue fv.wires s.basis=(if oldFrozen then st else zStep st).fv)
    (hready : ∀ L∈[a,b,c,d,e],L.Available st
      (run (mintHistoryControls frozen fire active fv.second sigma rb k) (m.drop cursor) s))
    (hout : ∀ L∈[a,b,c,d,e],L.output=port)
    (hfr : ∀ L∈[a,b,c,d,e],L.frozen.input=frozen)
    (hzero : s.basis port=false) (phase : Bool)
    (hphase : s.phase=(phase ^^ (m.getD ordinal false &&
      (!(!(oldFrozen || (!oldFrozen && armed && decide ((zStep st).g=0))) &&
        decide ((zStep st).z≤0) && decide ((2:Int)^7 ∣ (zStep st).fv)) && decide (bbit st=1))))) :
    let stored := !(oldFrozen || (!oldFrozen && armed && decide ((zStep st).g=0))) &&
      decide ((zStep st).z≤0) && decide ((2:Int)^7 ∣ (zStep st).fv)
    runWithTape (recoverBranch (cleanBranchProgram [a,b,c,d,e] p frozen fire active fv.second sigma port rb k)
      port ordinal) m cursor s=⟨phase,writeBit s.basis port (!stored && decide (bbit st=1))⟩ := by
  apply recoverBranch_cancel _ _ _ _ _ _ _ _ hphase
  simpa only [hzero,Bool.false_xor] using
    cleanBranchProgram_run p st hi hp a b c d e ha hb hc hd he frozen fire active sigma port fv rb k r hn hr hk hlt
      hport oldFrozen armed hfg hfirst s (m.drop cursor) hwork hfire0 hactive hsigma0 hfrozen hrecord hrow hready hout hfr

end ECDSAAdd.Arithmetic.Paper935
