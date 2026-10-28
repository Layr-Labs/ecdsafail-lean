import ECDSAAdd.Math.Divsteps.Recovery

namespace ECDSAAdd.Arithmetic.Paper935

/-- Ten address bits hold the five nonconstant low bits of each odd residue.
The result is the determinant-based recovery bit, computed independently
of a walk execution. -/
def residueBranchTable (p : Int) (depth address : Nat) : Bool :=
  decide (ECDSAAdd.Divsteps.bitk
    ((((p : ZMod (2^depth)) *
      (((2*(address%32)+1)*(2*(address/32)+1):Nat):ZMod (2^depth))⁻¹).val):Int)
    (depth-1)=1)

theorem residueBranchTable_branch (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1) (hz : st.z<0)
    (depth f q : Nat) (hfbound : f<32)
    (hd : depth=padicValInt 2 (ECDSAAdd.Divsteps.zStep st).fv)
    (hf : ((ECDSAAdd.Divsteps.zStep st).f : ZMod (2^depth))=((2*f+1:Nat):ZMod (2^depth)))
    (hq : (((ECDSAAdd.Divsteps.zStep st).fv/(2:Int)^depth:Int):ZMod (2^depth))=
      ((2*q+1:Nat):ZMod (2^depth))) :
    residueBranchTable p depth (f+32*q)=decide (ECDSAAdd.Divsteps.bbit st=1) := by
  have hm : (f+32*q)%32=f := by omega
  have hdiv : (f+32*q)/32=q := by omega
  have law := ECDSAAdd.Divsteps.ladder_det hi hp hz hd rfl
  rw [Int.cast_mul,hf,hq] at law
  unfold residueBranchTable
  rw [hm,hdiv,Nat.cast_mul,←law]

end ECDSAAdd.Arithmetic.Paper935
