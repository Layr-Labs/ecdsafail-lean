import ECDSAAdd.Arithmetic.Paper935.FrozenDepth
import ECDSAAdd.Arithmetic.Paper935.BranchRecoveryMath

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Add the swap and newly frozen classes, preserving their controls. -/
def finishBranch (sigma fire output : Wire) : Program :=
  [.CX sigma output,.X sigma,.CCX fire sigma output,.X sigma]

theorem finishBranch_run (sigma fire output : Wire) (hn : [sigma,fire,output].Nodup)
    (s : State) (m : List Bool) :
    run (finishBranch sigma fire output) m s=
      ⟨s.phase,writeBit s.basis output
        (s.basis output ^^ s.basis sigma ^^ (s.basis fire && !s.basis sigma))⟩ := by
  have hsf : sigma≠fire := by simpa using (show sigma≠fire ∧ sigma≠output from by simpa using (List.nodup_cons.mp hn).1).1
  have hso : sigma≠output := by simpa using (show sigma≠fire ∧ sigma≠output from by simpa using (List.nodup_cons.mp hn).1).2
  have hfo : fire≠output := by simpa using (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  simp only [finishBranch,run]
  congr 1
  funext w
  by_cases hw : w=sigma
  · subst w; simp [writeBit,hso,hso.symm]
  · by_cases ho : w=output
    · subst w; simp [writeBit,hsf.symm,hso,hso.symm,hfo]
    · simp [writeBit,hw,ho,hsf.symm,hso,hso.symm,hfo]

def finiteBranchProgram (layouts : List DepthLayout) (p : Int) (sigma fire output : Wire) : Program :=
  finiteDepthProgram layouts p ++ finishBranch sigma fire output

theorem finiteBranchProgram_run (p : Int) (st : ZState) (hi : Inv p st) (hp : p%2=1)
    (a b c d e : DepthLayout) (ha : a.low.length=2) (hb : b.low.length=3)
    (hc : c.low.length=4) (hd : d.low.length=5) (he : e.low.length=6)
    (sigma fire output : Wire) (hn : [sigma,fire,output].Nodup)
    (frozen armed : Bool) (hfg : frozen=true → st.g=0)
    (hfirst : frozen=false → armed=true → (zStep st).g=0 → st.g≠0)
    (s : State) (m : List Bool)
    (hready : ∀ L∈[a,b,c,d,e],L.Available st s)
    (hout : ∀ L∈[a,b,c,d,e],L.output=output)
    (hfr : ∀ L∈[a,b,c,d,e],s.basis L.frozen.input=
      (frozen || (!frozen && armed && decide ((zStep st).g=0))))
    (hsigma : s.basis sigma=(!frozen && decide (0≤st.z ∧ st.g%2=1)))
    (hfire : s.basis fire=(!frozen && armed && decide ((zStep st).g=0))) :
    let stored := !(frozen || s.basis fire) && decide ((zStep st).z≤0) && decide ((2:Int)^7 ∣ (zStep st).fv)
    run (finiteBranchProgram [a,b,c,d,e] p sigma fire output) m s=
      ⟨s.phase,writeBit s.basis output (s.basis output ^^ (!stored && decide (bbit st=1)))⟩ := by
  have hso : sigma≠output := by simpa using (show sigma≠fire ∧ sigma≠output from by simpa using (List.nodup_cons.mp hn).1).2
  have hfo : fire≠output := by simpa using (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  rw [finiteBranchProgram,run_append,run_take,
    finiteDepthProgram_available _ p st hi hp output _ s m hready hout hfr,
    finishBranch_run sigma fire output hn]
  simp only [writeBit,Function.update_self,Function.update_of_ne hso,Function.update_of_ne hfo,
    Function.update_idem]
  rw [finiteDepthMask_five st _ a b c d e ha hb hc hd he,hsigma,hfire]
  have h := branchRecovery_measured p st hi hp frozen armed hfg hfirst
  dsimp only at h ⊢
  simp only [Bool.xor_assoc] at h ⊢
  rw [h]

theorem finiteBranch_cancel (p : Int) (st : ZState) (hi : Inv p st) (hp : p%2=1)
    (a b c d e : DepthLayout) (ha : a.low.length=2) (hb : b.low.length=3)
    (hc : c.low.length=4) (hd : d.low.length=5) (he : e.low.length=6)
    (sigma fire output : Wire) (hn : [sigma,fire,output].Nodup)
    (frozen armed : Bool) (hfg : frozen=true → st.g=0)
    (hfirst : frozen=false → armed=true → (zStep st).g=0 → st.g≠0)
    (s : State) (m : List Bool)
    (hready : ∀ L∈[a,b,c,d,e],L.Available st s)
    (hout : ∀ L∈[a,b,c,d,e],L.output=output)
    (hfr : ∀ L∈[a,b,c,d,e],s.basis L.frozen.input=
      (frozen || (!frozen && armed && decide ((zStep st).g=0))))
    (hsigma : s.basis sigma=(!frozen && decide (0≤st.z ∧ st.g%2=1)))
    (hfire : s.basis fire=(!frozen && armed && decide ((zStep st).g=0)))
    (hzero : s.basis output=false) (ordinal cursor : Nat) (phase : Bool)
    (hphase : s.phase=(phase ^^ (m.getD ordinal false &&
      (!( !(frozen || s.basis fire) && decide ((zStep st).z≤0) && decide ((2:Int)^7 ∣ (zStep st).fv)) && decide (bbit st=1))))) :
    let stored := !(frozen || s.basis fire) && decide ((zStep st).z≤0) && decide ((2:Int)^7 ∣ (zStep st).fv)
    runWithTape (ECDSAAdd.Arithmetic.Divsteps.recoverBranch
      (finiteBranchProgram [a,b,c,d,e] p sigma fire output) output ordinal) m cursor s=
      ⟨phase,writeBit s.basis output (!stored && decide (bbit st=1))⟩ := by
  apply ECDSAAdd.Arithmetic.Divsteps.recoverBranch_cancel _ _ _ _ _ _ _ _ hphase
  simpa only [hzero,Bool.false_xor] using
    finiteBranchProgram_run p st hi hp a b c d e ha hb hc hd he sigma fire output hn
      frozen armed hfg hfirst s (m.drop cursor) hready hout hfr hsigma hfire

end ECDSAAdd.Arithmetic.Paper935
