import ECDSAAdd.Arithmetic.Divsteps.Activity
import ECDSAAdd.Arithmetic.Divsteps.ControlBits
import ECDSAAdd.Arithmetic.Divsteps.CounterUpdate

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- The physical swap predicate already excludes frozen states. No extra
AND gate with the activity bit is required by the counter interface. -/
theorem counterSwap_eq_swapControl (st : ZState) : counterSwap st=swapControl st := by
  by_cases hg : st.g=0
  · simp [counterSwap,counterActive,swapControl,hg]
  · simp [counterSwap,counterActive,swapControl,hg]

theorem swapControl_active (st : ZState) : swapControl st=true → activeControl st=true := by
  rw [←counterSwap_eq_swapControl]
  exact counterSwap_active st

/-- Prepare all three controls while retaining the original data and counter. -/
def prepareControls (one active zsign glow parity swap : Wire) (bs : List ZeroBit) : Program :=
  activityTag one active bs ++ branchTags zsign glow parity swap

theorem prepareControls_correct (one active zsign glow parity swap : Wire)
    (bs : List ZeroBit) (zlo gtail : List Wire)
    (hn : (one::active::bs.flatMap ZeroBit.wires).Nodup)
    (hcn : [active,zsign,glow,parity,swap].Nodup)
    (hinputs : bs.map ZeroBit.input=glow::gtail)
    (st : ZState) (s : State) (m : List Bool)
    (ho : s.basis one=false) (ha : s.basis active=false)
    (hp : s.basis parity=false) (hq : s.basis swap=false)
    (hw : ∀ b∈bs,s.basis b.work=false)
    (hz : signedRegValue (zlo++[zsign]) s.basis=st.z)
    (hg : signedRegValue (glow::gtail) s.basis=st.g) :
    run (prepareControls one active zsign glow parity swap bs) m s=
      ⟨s.phase,writeBit (writeBit (writeBit s.basis active (activeControl st))
        parity (parityControl st)) swap (swapControl st)⟩ := by
  let a := activityTag one active bs
  let t := run a m s
  let rest := m.drop (measurementCount a)
  have hag := activityTag_zState one active bs hn st s m ho ha hw (by rwa [hinputs])
  have hat := activityTag_correct one active bs hn s m ho hw
  have hac : decide (regValue (bs.map ZeroBit.input) s.basis≠0)=activeControl st := by
    rw [hat] at hag
    simpa [writeBit,ha] using hag
  have ht : t=⟨s.phase,writeBit s.basis active (activeControl st)⟩ := by
    simpa [t,a,ha,hac] using hat
  have hza : zsign≠active := by intro h; subst active; simp at hcn
  have hga : glow≠active := by intro h; subst active; simp at hcn
  have hpa : parity≠active := by intro h; subst active; simp at hcn
  have hqa : swap≠active := by intro h; subst active; simp at hcn
  have hp' : t.basis parity=false := by simpa [ht,writeBit,hpa] using hp
  have hq' : t.basis swap=false := by simpa [ht,writeBit,hqa] using hq
  have hbt := branchTags_correct zsign glow parity swap (List.nodup_cons.mp hcn).2 t rest hp' hq'
  have hpbit := parityControl_bit glow gtail st s.basis hg
  have hsbit := swapControl_bits zsign glow zlo gtail st s.basis hz hg
  rw [prepareControls,run_append,run_take]
  rw [hbt,ht]
  simp only [writeBit,Function.update_apply,hga,hza,if_false]
  rw [hpbit,←hsbit]
  rw [←hpbit]

theorem prepareControls_counts (one active zsign glow parity swap : Wire)
    (bs : List ZeroBit) :
    toffoliCount (prepareControls one active zsign glow parity swap bs)=bs.length+1 ∧
    measurementCount (prepareControls one active zsign glow parity swap bs)=bs.length := by
  simp [prepareControls,toffoliCount_append,measurementCount_append,
    (activityTag_counts one active bs).1,(activityTag_counts one active bs).2,
    (branchTags_resources zsign glow parity swap).1,(branchTags_resources zsign glow parity swap).2.1]

/-- Counter interface using exactly the controls produced above, with range
obligations obtained from the same state bounds as the row body. -/
theorem counterUpdate_zSlot (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) (hw : 2≤z.length)
    (st : ZState) (pB zB cB : Int) (hbnd : Bounds pB zB cB st)
    (hfit : zB+1<((2^(z.length-1):Nat):Int))
    (s : State) (m : List Bool)
    (ha : s.basis active=activeControl st) (hs : s.basis swap=swapControl st)
    (hzero : regValue zero s.basis=0) (hvalue : signedRegValue z s.basis=st.z)
    (hcarry : regValue carry s.basis=0) :
    (run (counterUpdate active swap zero z carry) m s).phase=s.phase ∧
    (∀ w, w∉z → (run (counterUpdate active swap zero z carry) m s).basis w=s.basis w) ∧
    signedRegValue z (run (counterUpdate active swap zero z carry) m s).basis=(zSlot st).z := by
  have hnext : counterNext (activeControl st) (swapControl st) st.z=(zSlot st).z := by
    rw [←counterSwap_eq_swapControl]
    exact counterNext_zStep st
  have hb : -((2^(z.length-1):Nat):Int)≤counterNext (activeControl st) (swapControl st) st.z ∧
      counterNext (activeControl st) (swapControl st) st.z<((2^(z.length-1):Nat):Int) := by
    have hlo := hbnd.z_lo
    have hhi := hbnd.z_hi
    cases activeControl st <;> cases swapControl st <;>
      simp only [counterNext,Bool.false_eq_true,if_false,if_true] <;> constructor <;> omega
  obtain ⟨hp,ho⟩ := counterUpdate_int_spec active swap zero z carry hn hz hc hw
    (activeControl st) (swapControl st) st.z (swapControl_active st) hb.1 hb.2 s m
    ⟨ha,hs,hzero,hvalue,hcarry⟩
  exact ⟨hp,counterUpdate_frame active swap zero z carry hn hz hc s m hzero hcarry,
    ho.2.2.2.1.trans hnext⟩

end ECDSAAdd.Arithmetic.Divsteps
