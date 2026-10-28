import ECDSAAdd.Arithmetic.SignedWordBits
import ECDSAAdd.Math.Divsteps.RowBounds

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Copy parity and compute the swap branch from the signed counter's high bit.
The temporarily inverted sign wire is restored. Both targets start clean. -/
def branchTags (zsign glow parity swap : Wire) : Program :=
  [.CX glow parity,.X zsign,.CCX zsign parity swap,.X zsign]

theorem branchTags_correct (zsign glow parity swap : Wire)
    (hn : [zsign,glow,parity,swap].Nodup) (s : State) (m : List Bool)
    (hp : s.basis parity=false) (hq : s.basis swap=false) :
    run (branchTags zsign glow parity swap) m s=
      ⟨s.phase,writeBit (writeBit s.basis parity (s.basis glow)) swap
        (!s.basis zsign && s.basis glow)⟩ := by
  have hzp : zsign≠parity := by simp_all
  have hzq : zsign≠swap := by simp_all
  have hgp : glow≠parity := by simp_all
  have hpq : parity≠swap := by simp_all
  have hpz := Ne.symm hzp
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hwz : w=zsign
  · subst w
    cases hz : s.basis zsign <;> cases hg : s.basis glow <;>
      simp_all [writeBit]
  · by_cases hwp : w=parity
    · subst w
      simp_all [writeBit]
    · by_cases hwq : w=swap
      · subst w
        cases hz : s.basis zsign <;> cases hg : s.basis glow <;>
          simp_all [writeBit]
      · simp_all [writeBit]

theorem branchTags_resources (zsign glow parity swap : Wire) :
    toffoliCount (branchTags zsign glow parity swap)=1 ∧
    measurementCount (branchTags zsign glow parity swap)=0 ∧
    wires (branchTags zsign glow parity swap)=[zsign,glow,parity,swap].toFinset := by
  refine ⟨rfl,rfl,?_⟩
  ext w
  simp [branchTags,wires,Instr.wires]
  tauto

/-- Parity is read from the physical low bit for positive and negative words. -/
theorem parityControl_bit (low : Wire) (tail : List Wire) (st : ECDSAAdd.Divsteps.ZState)
    (s : BasisState) (hg : signedRegValue (low::tail) s=st.g) :
    s low=ECDSAAdd.Divsteps.parityControl st := by
  have he := signedRegValue_even_iff low tail s
  rw [hg] at he
  have hmod : st.g%2=0 ∨ st.g%2=1 := by omega
  unfold ECDSAAdd.Divsteps.parityControl
  cases hb : s low <;> simp [hb] at he ⊢ <;> omega

/-- The sign/low-bit predicate is exactly the integer divstep swap condition. -/
theorem swapControl_bits (zsign glow : Wire) (zlo gtail : List Wire)
    (st : ECDSAAdd.Divsteps.ZState) (s : BasisState)
    (hz : signedRegValue (zlo++[zsign]) s=st.z)
    (hg : signedRegValue (glow::gtail) s=st.g) :
    (!s zsign && s glow)=ECDSAAdd.Divsteps.swapControl st := by
  have hsign := signedRegValue_neg_iff zlo zsign s
  rw [hz] at hsign
  rw [parityControl_bit glow gtail st s hg]
  unfold ECDSAAdd.Divsteps.swapControl ECDSAAdd.Divsteps.parityControl
  cases hb : s zsign <;> simp [hb] at hsign ⊢ <;> omega

theorem branchTags_zState (zsign glow parity swap : Wire) (zlo gtail : List Wire)
    (hn : [zsign,glow,parity,swap].Nodup)
    (st : ECDSAAdd.Divsteps.ZState) (s : State) (m : List Bool)
    (hp : s.basis parity=false) (hq : s.basis swap=false)
    (hz : signedRegValue (zlo++[zsign]) s.basis=st.z)
    (hg : signedRegValue (glow::gtail) s.basis=st.g) :
    (run (branchTags zsign glow parity swap) m s).basis parity=ECDSAAdd.Divsteps.parityControl st ∧
    (run (branchTags zsign glow parity swap) m s).basis swap=ECDSAAdd.Divsteps.swapControl st := by
  have hpq : parity≠swap := by simp_all
  rw [branchTags_correct zsign glow parity swap hn s m hp hq]
  simp only [writeBit,Function.update_apply,hpq,if_false,ite_true]
  exact ⟨parityControl_bit glow gtail st s.basis hg,swapControl_bits zsign glow zlo gtail st s.basis hz hg⟩

theorem branchTags_qubits (zsign glow parity swap : Wire)
    (hn : [zsign,glow,parity,swap].Nodup) :
    qubitCount (branchTags zsign glow parity swap)=4 := by
  rw [qubitCount,(branchTags_resources zsign glow parity swap).2.2,
    List.toFinset_card_of_nodup hn]
  rfl

end ECDSAAdd.Arithmetic.Divsteps
