import ECDSAAdd.Arithmetic.Paper935.BranchAssembly

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

private theorem mask_partition (f c sig b gate : Bool) (h : (f ^^ c)=!sig) :
    ((gate && f && b) ^^ (gate && c && b))=(gate && !sig && b) := by
  cases f <;> cases c <;> cases sig <;> cases b <;> cases gate <;> simp_all

private theorem mask_cancel (a c sig fire b : Bool)
    (h : ((a ^^ (c && b)) ^^ sig ^^ (fire && !sig))=b) :
    (a ^^ sig ^^ (fire && !sig))=(!c && b) := by
  cases a <;> cases c <;> cases sig <;> cases fire <;> cases b <;> simp_all

/-- Before the stored record is popped, finite decoding plus swap/freeze
reconstructs exactly the branch that was actually measured, namely zero on a
stored lane. Thus its phase correction must precede the pop. -/
theorem branchRecovery_measured (p : Int) (st : ZState) (hi : Inv p st) (hp : p%2=1)
    (frozen armed : Bool) (hfg : frozen=true → st.g=0)
    (hfirst : frozen=false → armed=true → (zStep st).g=0 → st.g≠0) :
    let fire := !frozen && armed && decide ((zStep st).g=0)
    let sigma := !frozen && decide (0≤st.z ∧ st.g%2=1)
    let gate := !(frozen || fire) && decide ((zStep st).z≤0)
    let finite := gate && decide (2≤padicValInt 2 (zStep st).fv ∧ padicValInt 2 (zStep st).fv≤6) && decide (bbit st=1)
    let stored := gate && decide ((2:Int)^7 ∣ (zStep st).fv)
    (finite ^^ sigma ^^ (fire && !sigma))=(!stored && decide (bbit st=1)) := by
  dsimp only
  cases hz : frozen with
  | true => simp [bbit,hfg hz]
  | false =>
    have part := mask_partition _ _ _ (decide (bbit st=1))
      (!(false || (!false && armed && decide ((zStep st).g=0))) && decide ((zStep st).z≤0))
      (branchDepth_partition p st hi hp)
    have assembled := branchAssembly_value st hi.fodd false armed (by simp) (by simpa [hz] using hfirst)
    dsimp only at assembled
    apply mask_cancel
    simp only [Bool.not_false,Bool.true_and,Bool.false_or] at part assembled ⊢
    rw [part]
    simpa [Bool.and_assoc,Bool.and_left_comm,Bool.and_comm] using assembled

end ECDSAAdd.Arithmetic.Paper935
