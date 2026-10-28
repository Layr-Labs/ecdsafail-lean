import ECDSAAdd.Arithmetic.Paper935.ClassLookup
import ECDSAAdd.Arithmetic.Paper935.RecoveryLookup

namespace ECDSAAdd.Arithmetic.Paper935

/-- The physically selected finite-depth lookup returns the real old branch.
On unselected lanes its value is immaterial, and the enable makes it zero. -/
theorem depthLookup_selected_branch (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1)
    (sign frozen flow vlow address qlow : Wire) (zb low : List ZeroBit)
    (zlo vtail fdata ftail slice qbits qtail : List Wire) (s : BasisState)
    (hzview : zb.map ZeroBit.input=zlo++[sign]) (hvtail : vtail≠[])
    (hmin : 2≤low.length) (hmax : low.length≤6)
    (hflen : fdata.length=4) (hqlen : qbits.length=5) (hslen : slice.length=low.length)
    (hftail : ftail≠[]) (hqtail : qtail≠[])
    (hz : signedRegValue (zlo++[sign]) s=(ECDSAAdd.Divsteps.zStep st).z)
    (hv : signedRegValue (vlow::(low.map ZeroBit.input++vtail)) s=(ECDSAAdd.Divsteps.zStep st).fv)
    (hf : signedRegValue (flow::((address::fdata)++ftail)) s=(ECDSAAdd.Divsteps.zStep st).f)
    (hcoeffview : vlow::(low.map ZeroBit.input++vtail)=slice++(qlow::(qbits++qtail))) :
    ((!s frozen && !(!s sign && !decide (regValue (zb.map ZeroBit.input) s=0)) &&
      decide (regValue (low.map ZeroBit.input) s=2^(low.length-1))) &&
      residueBranchTable p low.length (regValue (address::(fdata++qbits)) s))=
    ((!s frozen && decide ((ECDSAAdd.Divsteps.zStep st).z≤0) &&
      decide (padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv=low.length)) &&
      decide (ECDSAAdd.Divsteps.bbit st=1)) := by
  rw [historyDepth_predicate_value sign frozen vlow zb low zlo vtail s
    (ECDSAAdd.Divsteps.zStep st) hzview hvtail (by omega) hz hv (hi.zStep hp).fveven]
  let selected := !s frozen && decide ((ECDSAAdd.Divsteps.zStep st).z≤0) &&
    decide (padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv=low.length)
  change (selected && _ )=(selected && _)
  cases hsel : selected with
  | false => rfl
  | true =>
    have hh := Bool.and_eq_true_iff.mp hsel
    have hcounter : (ECDSAAdd.Divsteps.zStep st).z≤0 :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hh.1).2
    have hdepth : low.length=padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv :=
      (of_decide_eq_true hh.2).symm
    have hdiv : (2:Int)^low.length ∣ (ECDSAAdd.Divsteps.zStep st).fv :=
      (historyCutoff_valuation _ low.length).mpr (Or.inr (by omega))
    have hneg := (historyCutoff_class p st hi hp low.length hmin hcounter hdiv).2
    have hq : signedRegValue (slice++(qlow::(qbits++qtail))) s=(ECDSAAdd.Divsteps.zStep st).fv := by
      rw [←hcoeffview]; exact hv
    rw [recoveryLookup_table p st hi hp hneg low.length hdepth hmax flow address qlow
      fdata ftail slice qbits qtail s hflen hqlen hslen hftail hqtail hf hq]

theorem depthLookup_run (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (one zz pos sign flag address tmp output : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit)
    (fdata qbits scratch : List Wire)
    (hnz : (flag::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::flag::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
    (hworkpos : ∀ b∈frozen::positive::low,b.work≠pos)
    (hnlookup : (flag::output::address::((fdata++qbits)++scratch++[tmp])).Nodup)
    (hflen : fdata.length=4) (hqlen : qbits.length=5) (hs : scratch.length=9)
    (hflag : flag∉[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires)
    (hout : output∉[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires)
    (s : State) (m : List Bool) (hone : s.basis one=true)
    (hzz : s.basis zz=false) (hpzero : s.basis pos=false)
    (hzw : ∀ b∈zb,s.basis b.work=false)
    (hfw : ∀ b∈frozen::positive::low,s.basis b.work=false)
    (hflag0 : s.basis flag=false)
    (htmp : s.basis tmp=false) (hwork : ∀ w∈scratch,s.basis w=false) 
    (flow vlow qlow : Wire) (zlo vtail ftail slice qtail : List Wire)
    (hzview : zb.map ZeroBit.input=zlo++[sign]) (hvtail : vtail≠[])
    (hmin : 2≤low.length) (hmax : low.length≤6) (hslen : slice.length=low.length)
    (hftail : ftail≠[]) (hqtail : qtail≠[])
    (hzval : signedRegValue (zlo++[sign]) s.basis=(ECDSAAdd.Divsteps.zStep st).z)
    (hvval : signedRegValue (vlow::(low.map ZeroBit.input++vtail)) s.basis=(ECDSAAdd.Divsteps.zStep st).fv)
    (hfval : signedRegValue (flow::((address::fdata)++ftail)) s.basis=(ECDSAAdd.Divsteps.zStep st).f)
    (hcoeffview : vlow::(low.map ZeroBit.input++vtail)=slice++(qlow::(qbits++qtail))) :
    run (classLookup one zz pos sign flag address tmp output zb frozen positive low (2^(low.length-1))
      (fdata++qbits) scratch (residueBranchTable p low.length)) m s=
      ⟨s.phase,writeBit s.basis output (s.basis output ^^
        ((!s.basis frozen.input && decide ((ECDSAAdd.Divsteps.zStep st).z≤0) &&
          decide (padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv=low.length)) &&
          decide (ECDSAAdd.Divsteps.bbit st=1)))⟩ := by
  have hfit : 2^(low.length-1)<2^low.length := by
    have he : low.length=(low.length-1)+1 := by omega
    conv_rhs => rw [he,pow_succ]
    have hh := Nat.two_pow_pos (low.length-1)
    omega
  rw [classLookup_run one zz pos sign flag address tmp output zb frozen positive low (2^(low.length-1))
    (fdata++qbits) scratch (residueBranchTable p low.length) hnz hnf hsg hpos hfr hlow hworkpos hnlookup
    (by simp [hflen,hqlen]) hs hflag hout s m hone hzz hpzero hzw hfw hfit hflag0 htmp hwork,
    depthLookup_selected_branch p st hi hp sign frozen.input flow vlow address qlow zb low
      zlo vtail fdata ftail slice qbits qtail s.basis hzview hvtail hmin hmax hflen hqlen hslen hftail hqtail hzval hvval hfval hcoeffview]

end ECDSAAdd.Arithmetic.Paper935
