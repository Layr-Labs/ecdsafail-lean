import ECDSAAdd.Arithmetic.Paper935.PostInverse
import ECDSAAdd.Framework.MeasuredLocality

namespace ECDSAAdd.Arithmetic.Paper935

private theorem state_eq {a b : State} (h : a.phase=b.phase) (hb : a.basis=b.basis) : a=b := by
  cases a; cases b; simp_all

/-- Reconstruct old activity from final frozen and newly fired flags, then
reconstruct swap from the second updated coefficient bit. -/
def historyControlCore (frozen fire active second sigma : Wire) : Program :=
  [.X active,.CX frozen active,.CX fire active,.CCX active second sigma]

theorem historyControlCore_proper (frozen fire active second sigma : Wire)
    (hn : [frozen,fire,active,second,sigma].Nodup) :
    ProperProgram (historyControlCore frozen fire active second sigma) := by
  have haf : frozen≠active := by simp_all
  have har : fire≠active := by simp_all
  have haq : active≠sigma := by simp_all
  have hsq : second≠sigma := by simp_all
  simp [historyControlCore,ProperProgram,ProperGate,haf,har,haq,hsq]

theorem historyControlCore_run (frozen fire active second sigma : Wire)
    (hn : [frozen,fire,active,second,sigma].Nodup) (s : State) (m : List Bool)
    (ha : s.basis active=false) (hq : s.basis sigma=false) :
    run (historyControlCore frozen fire active second sigma) m s=
      ⟨s.phase,writeBit (writeBit s.basis active (!s.basis frozen ^^ s.basis fire)) sigma
        ((!s.basis frozen ^^ s.basis fire) && s.basis second)⟩ := by
  have hfa : frozen≠active := by simp_all
  have hra : fire≠active := by simp_all
  have hsa : second≠active := Ne.symm (by simp_all : active≠second)
  have hqa : sigma≠active := Ne.symm (by simp_all : active≠sigma)
  simp [historyControlCore,run,writeBit,ha,hq,hfa,hra,hsa,hqa]

def mintHistoryControls (frozen fire active second sigma : Wire) (rb : List ZeroBit) (k : Nat) : Program :=
  equalConstant frozen fire rb k ++ historyControlCore frozen fire active second sigma

def clearHistoryControls (frozen fire active second sigma : Wire) (rb : List ZeroBit) (k : Nat) : Program :=
  (historyControlCore frozen fire active second sigma).reverse ++ equalConstant frozen fire rb k

theorem mintHistoryControls_run (frozen fire active second sigma : Wire) (rb : List ZeroBit) (k : Nat)
    (hn : [frozen,fire,active,second,sigma].Nodup)
    (hr : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length)
    (s : State) (m : List Bool) (hc : ∀ b∈rb,s.basis b.work=false)
    (hfire : s.basis fire=false) (ha : s.basis active=false) (hq : s.basis sigma=false) :
    let fired := s.basis frozen && decide (regValue (rb.map ZeroBit.input) s.basis=k)
    let alive := !s.basis frozen ^^ fired
    run (mintHistoryControls frozen fire active second sigma rb k) m s=
      ⟨s.phase,writeBit (writeBit (writeBit s.basis fire fired) active alive) sigma
        (alive && s.basis second)⟩ := by
  have hfa : active≠fire := Ne.symm (by simp_all : fire≠active)
  have hqf : sigma≠fire := Ne.symm (by simp_all : fire≠sigma)
  have hsf : second≠fire := Ne.symm (by simp_all : fire≠second)
  have hff : frozen≠fire := by simp_all
  rw [mintHistoryControls,run_append,run_take,equalConstant_correct frozen fire rb k hr hk s m hc]
  simp only [hfire,Bool.false_xor]
  rw [historyControlCore_run frozen fire active second sigma hn _ _
    (by simpa [writeBit,hfa] using ha) (by simpa [writeBit,hqf] using hq)]
  simp [writeBit,hff,hsf]

theorem historyControls_roundtrip (frozen fire active second sigma : Wire) (rb : List ZeroBit) (k : Nat)
    (hn : [frozen,fire,active,second,sigma].Nodup)
    (hr : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length)
    (s : State) (m n : List Bool) (hc : ∀ b∈rb,s.basis b.work=false) :
    run (clearHistoryControls frozen fire active second sigma rb k) n
      (run (mintHistoryControls frozen fire active second sigma rb k) m s)=s := by
  rw [mintHistoryControls,clearHistoryControls,run_append,run_take,run_append,run_take,
    run_reverse_proper _ (historyControlCore_proper frozen fire active second sigma hn)]
  exact equalConstant_roundtrip frozen fire rb k hr hk s m _ hc

private theorem run_write_outside (p : Program) (port : Wire) (hp : port∉wires p)
    (s : State) (b : Bool) (m : List Bool) :
    run p m ⟨s.phase,writeBit s.basis port b⟩=
      ⟨(run p m s).phase,writeBit (run p m s).basis port b⟩ := by
  have loc := run_measured_locality p (wires p) (by rfl)
    ⟨s.phase,writeBit s.basis port b⟩ s m rfl (by
      intro w hw
      exact Function.update_of_ne (show w≠port from fun he => hp (he ▸ hw)) _ _)
  apply state_eq
  · exact loc.1
  · funext w
    by_cases hw : w∈wires p
    · change _ = writeBit (run p m s).basis port b w
      rw [show writeBit (run p m s).basis port b w=(run p m s).basis w from
        Function.update_of_ne (show w≠port from fun he => hp (he ▸ hw)) _ _]
      exact loc.2 w hw
    · rw [run_preserves_outside p m _ w hw]
      by_cases he : w=port
      · subst w; simp [writeBit]
      · simp only [writeBit,Function.update_of_ne he]
        exact (run_preserves_outside p m s w hw).symm

/-- The controls can be released after a decoder changes only its distinct
output wire. This applies to measured cleanup with a fresh independent tape. -/
theorem historyControls_clear_after_write (frozen fire active second sigma port : Wire)
    (rb : List ZeroBit) (k : Nat)
    (hn : [frozen,fire,active,second,sigma].Nodup)
    (hr : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length)
    (hp : port∉wires (clearHistoryControls frozen fire active second sigma rb k))
    (s : State) (m n : List Bool) (hc : ∀ b∈rb,s.basis b.work=false) (b : Bool) :
    let t := run (mintHistoryControls frozen fire active second sigma rb k) m s
    run (clearHistoryControls frozen fire active second sigma rb k) n
      ⟨t.phase,writeBit t.basis port b⟩=⟨s.phase,writeBit s.basis port b⟩ := by
  dsimp only
  rw [run_write_outside _ port hp,
    historyControls_roundtrip frozen fire active second sigma rb k hn hr hk s m n hc]

end ECDSAAdd.Arithmetic.Paper935
