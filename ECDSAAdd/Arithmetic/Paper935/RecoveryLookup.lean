import ECDSAAdd.Arithmetic.Paper935.LookupBranch
import ECDSAAdd.Arithmetic.Paper935.ResidueBranch
import ECDSAAdd.Arithmetic.Paper935.ResidueWires

namespace ECDSAAdd.Arithmetic.Paper935

/-- An actual bounded-workspace decoder for every negative-counter recovery
depth at most six, including the previously missing depths five and six. -/
def recoveryLookup (p : Int) (depth : Nat) (flag address tmp output : Wire)
    (fdata qbits scratch : List Wire) : Program :=
  lookupBranch flag address tmp output (fdata++qbits) scratch (residueBranchTable p depth)

theorem recoveryLookup_table (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (hz : st.z<0)
    (depth : Nat) (hd : depth=padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv) (hdepth : depth≤6)
    (flow address qlow : Wire) (fdata ftail slice qbits qtail : List Wire) (s : BasisState)
    (hflen : fdata.length=4) (hqlen : qbits.length=5) (hslen : slice.length=depth)
    (hftail : ftail≠[]) (hqtail : qtail≠[])
    (hf : signedRegValue (flow::((address::fdata)++ftail)) s=(ECDSAAdd.Divsteps.zStep st).f)
    (hq : signedRegValue (slice++(qlow::(qbits++qtail))) s=(ECDSAAdd.Divsteps.zStep st).fv) :
    residueBranchTable p depth (regValue (address::(fdata++qbits)) s)=
      decide (ECDSAAdd.Divsteps.bbit st=1) := by
  have hfl : (address::fdata).length=5 := by simp [hflen]
  have hres := recoveryResidues_physical p st hi hp hz depth hd hdepth flow qlow
    (address::fdata) ftail slice qbits qtail s hfl hqlen hslen hftail hqtail hf hq
  have hbound : regValue (address::fdata) s<32 := by
    have h := regValue_lt (address::fdata) s
    simpa only [hfl] using h
  have hm := residueBranchTable_branch p st hi hp hz depth
    (regValue (address::fdata) s) (regValue qbits s) hbound hd hres.1 hres.2
  rw [←List.cons_append,regValue_append,hfl]
  exact hm

theorem recoveryLookup_run (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (hz : st.z<0)
    (depth : Nat) (hd : depth=padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv) (hdepth : depth≤6)
    (flag flow address qlow tmp output : Wire) (fdata ftail slice qbits qtail scratch : List Wire)
    (hn : (flag::output::address::((fdata++qbits)++scratch++[tmp])).Nodup)
    (hflen : fdata.length=4) (hqlen : qbits.length=5) (hslen : slice.length=depth)
    (hscratch : scratch.length=9) (hftail : ftail≠[]) (hqtail : qtail≠[])
    (s : State) (m : List Bool) (ht : s.basis tmp=false) (hwork : ∀ w∈scratch,s.basis w=false)
    (hf : signedRegValue (flow::((address::fdata)++ftail)) s.basis=(ECDSAAdd.Divsteps.zStep st).f)
    (hq : signedRegValue (slice++(qlow::(qbits++qtail))) s.basis=(ECDSAAdd.Divsteps.zStep st).fv) :
    run (recoveryLookup p depth flag address tmp output fdata qbits scratch) m s=
      ⟨s.phase,writeBit s.basis output (s.basis output ^^
        (s.basis flag && decide (ECDSAAdd.Divsteps.bbit st=1)))⟩ := by
  rw [recoveryLookup,lookupBranch_run flag address tmp output (fdata++qbits) scratch
    (residueBranchTable p depth) hn (by simp [hflen,hqlen]) hscratch s m ht hwork,
    recoveryLookup_table p st hi hp hz depth hd hdepth flow address qlow fdata ftail slice qbits qtail s.basis hflen hqlen hslen hftail hqtail hf hq]

theorem recoveryLookup_cancel (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (hz : st.z<0)
    (depth : Nat) (hd : depth=padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv) (hdepth : depth≤6)
    (flag flow address qlow tmp output : Wire) (fdata ftail slice qbits qtail scratch : List Wire)
    (hn : (flag::output::address::((fdata++qbits)++scratch++[tmp])).Nodup)
    (hflen : fdata.length=4) (hqlen : qbits.length=5) (hslen : slice.length=depth)
    (hscratch : scratch.length=9) (hftail : ftail≠[]) (hqtail : qtail≠[])
    (s : State) (m : List Bool) (ht : s.basis tmp=false) (hwork : ∀ w∈scratch,s.basis w=false)
    (hf : signedRegValue (flow::((address::fdata)++ftail)) s.basis=(ECDSAAdd.Divsteps.zStep st).f)
    (hq : signedRegValue (slice++(qlow::(qbits++qtail))) s.basis=(ECDSAAdd.Divsteps.zStep st).fv)
    (henable : s.basis flag=true) (hout : s.basis output=false)
    (ordinal cursor : Nat) (phase : Bool)
    (hphase : s.phase=(phase ^^ (m.getD ordinal false && decide (ECDSAAdd.Divsteps.bbit st=1)))) :
    runWithTape (ECDSAAdd.Arithmetic.Divsteps.recoverBranch
      (recoveryLookup p depth flag address tmp output fdata qbits scratch) output ordinal) m cursor s=
      ⟨phase,writeBit s.basis output (decide (ECDSAAdd.Divsteps.bbit st=1))⟩ := by
  apply ECDSAAdd.Arithmetic.Divsteps.recoverBranch_cancel _ _ _ _ _ _ _ _ hphase
  rw [recoveryLookup_run p st hi hp hz depth hd hdepth flag flow address qlow tmp output
    fdata ftail slice qbits qtail scratch hn hflen hqlen hslen hscratch hftail hqtail s (m.drop cursor) ht hwork hf hq,
    henable,hout]
  simp


theorem recoveryLookup_counts (p : Int) (depth : Nat) (flag address tmp output : Wire)
    (fdata qbits scratch : List Wire) (hf : fdata.length=4) (hq : qbits.length=5) (hs : scratch.length=9) :
    toffoliCount (recoveryLookup p depth flag address tmp output fdata qbits scratch)=2045 ∧
    measurementCount (recoveryLookup p depth flag address tmp output fdata qbits scratch)=2044 :=
  lookupBranch_counts flag address tmp output (fdata++qbits) scratch (residueBranchTable p depth)
    (by simp [hf,hq]) hs

theorem recoveryLookup_wireBound (p : Int) (depth : Nat) (flag address tmp output : Wire)
    (fdata qbits scratch : List Wire) (hf : fdata.length=4) (hq : qbits.length=5) (hs : scratch.length=9) :
    (wires (recoveryLookup p depth flag address tmp output fdata qbits scratch)).card≤22 :=
  lookupBranch_wireBound flag address tmp output (fdata++qbits) scratch (residueBranchTable p depth)
    (by simp [hf,hq]) hs

end ECDSAAdd.Arithmetic.Paper935
