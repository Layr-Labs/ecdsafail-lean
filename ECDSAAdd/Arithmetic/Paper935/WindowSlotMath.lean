import ECDSAAdd.Arithmetic.Paper935.WindowStep
import ECDSAAdd.Arithmetic.Paper935.PublicPost

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

theorem pinStep_rows (tmin t : Nat) (u : PinState) :
    (pinStep tmin t u).rows=(if u.frozen then u.rows else ECDSAAdd.Divsteps.zStep u.rows) := by
  unfold pinStep
  split_ifs
  · rfl
  · dsimp only; split_ifs <;> rfl

theorem pinnedCounter_value (st : ECDSAAdd.Divsteps.ZState) (frozen : Bool)
    (n x : Nat) (hn : 2≤n) (hx : x<2^n) (hdecode : signedDecode n x=st.z)
    (hzero : frozen=true → st.g=0)
    (hfit : PayloadFits (n-1) (if frozen then st else ECDSAAdd.Divsteps.zStep st).z) :
    signedDecode n (counterWord n (!frozen) (decide (0≤st.z ∧ st.g%2=1)) x)=
      (if frozen then st else ECDSAAdd.Divsteps.zStep st).z := by
  have relation : decide (0≤st.z ∧ st.g%2=1)=true → (!frozen)=true := by
    cases frozen <;> simp_all
  have next : counterNext (!frozen) (decide (0≤st.z ∧ st.g%2=1)) st.z=
      (if frozen then st else ECDSAAdd.Divsteps.zStep st).z := by
    cases frozen with
    | false =>
      simp only [Bool.not_false,counterNext,ite_true,decide_eq_true_eq]
      unfold ECDSAAdd.Divsteps.zStep
      split_ifs <;> first | contradiction | rfl
    | true => simp [counterNext]
  have h := counterWord_signed n (!frozen) (decide (0≤st.z ∧ st.g%2=1)) x hn hx relation
    (by rw [hdecode,next]; exact hfit.1) (by rw [hdecode,next]; exact hfit.2)
  rwa [hdecode,next] at h

end ECDSAAdd.Arithmetic.Paper935
