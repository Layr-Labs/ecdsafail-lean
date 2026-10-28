import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Arithmetic.SkywalkIntegerLoopCore

namespace ECDSAAdd.Arithmetic

def phaseShift (d : Bool) (s : State) : State := ⟨s.phase ^^ d,s.basis⟩

private theorem xor_reorder (a b c : Bool) : ((a ^^ b) ^^ c)=((a ^^ c) ^^ b) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem correct_phaseShift (cs : List Correction) (d : Bool) (s : State) :
    correct cs (phaseShift d s)=phaseShift d (correct cs s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | Z q =>
      simp only [correct,phaseShift]
      rw [xor_reorder]
      exact ih ⟨s.phase ^^ s.basis q,s.basis⟩
    | CZ a b =>
      simp only [correct,phaseShift]
      rw [xor_reorder]
      exact ih ⟨s.phase ^^ (s.basis a && s.basis b),s.basis⟩

theorem measure_phaseShift (q : Wire) (c0 c1 : List Correction)
    (d m : Bool) (s : State) :
    measureAndCorrect q c0 c1 m (phaseShift d s)=
      phaseShift d (measureAndCorrect q c0 c1 m s) := by
  unfold measureAndCorrect
  change correct _ ⟨(s.phase ^^ d) ^^ (m && s.basis q),writeBit s.basis q false⟩=_
  rw [xor_reorder]
  exact correct_phaseShift (if m then c1 else c0) d
    ⟨s.phase ^^ (m && s.basis q),writeBit s.basis q false⟩

theorem run_phaseShift (p : Program) (m : List Bool) (d : Bool) (s : State) :
    run p m (phaseShift d s)=phaseShift d (run p m s) := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X q =>
      simpa only [run,phaseShift] using ih m ⟨s.phase,writeBit s.basis q (!s.basis q)⟩
    | CX a q =>
      simpa only [run,phaseShift] using ih m ⟨s.phase,writeBit s.basis q (s.basis q ^^ s.basis a)⟩
    | CCX a b q =>
      simpa only [run,phaseShift] using ih m
        ⟨s.phase,writeBit s.basis q (s.basis q ^^ (s.basis a && s.basis b))⟩
    | measureX q c0 c1 =>
      simp only [run]
      rw [measure_phaseShift]
      exact ih m.tail (measureAndCorrect q c0 c1 (m.headD false) s)

/-- Basis behavior is independent of the supplied measurement outcomes.
Outcome dependence is confined to the separately tracked phase. -/
theorem run_basis_records (p : Program) (s t : State) (m n : List Bool)
    (hb : s.basis=t.basis) : (run p m s).basis=(run p n t).basis := by
  induction p generalizing s t m n with
  | nil => exact hb
  | cons i p ih =>
    cases i <;> simp only [run]
    all_goals apply ih
    all_goals first
      | simp only [hb]
      | simp only [measureAndCorrect,correct_basis,hb]

/-- Local basis agreement preserves the circuit's phase increment, even when
the surrounding caller states have different incoming phases. -/
theorem run_local_increment (p : Program) (s t : State) (m : List Bool)
    (hb : ∀ q∈wires p,s.basis q=t.basis q) :
    ((run p m s).phase ^^ s.phase)=((run p m t).phase ^^ t.phase) ∧
    ∀ q∈wires p,(run p m s).basis q=(run p m t).basis q := by
  let d := s.phase ^^ t.phase
  let u := phaseShift d t
  have ph : s.phase=u.phase := by
    change s.phase=(t.phase ^^ (s.phase ^^ t.phase))
    cases s.phase <;> cases t.phase <;> rfl
  have hbits : ∀ q∈wires p,s.basis q=u.basis q := hb
  have hr := pool_run_agrees p (wires p) (Finset.Subset.refl _) m s u ph hbits
  have hu : run p m u=phaseShift d (run p m t) := run_phaseShift p m d t
  rw [hu] at hr
  have hp : (run p m s).phase=((run p m t).phase ^^ (s.phase ^^ t.phase)) := hr.1
  refine ⟨?_,hr.2⟩
  rw [hp]
  cases s.phase <;> cases t.phase <;> cases (run p m t).phase <;> rfl

private theorem phase_commutation (a b c d e : Bool)
    (h1 : (a ^^ b)=(c ^^ d)) (h2 : (e ^^ c)=(b ^^ d)) : a=e := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all

/-- Disjoint gate supports commute, including their measurement corrections.
Each block retains its own independent record list. -/
theorem run_disjoint_commute (p q : Program) (hd : Disjoint (wires p) (wires q))
    (mp mq : List Bool) (s : State) :
    run p mp (run q mq s)=run q mq (run p mp s) := by
  have pRead : ∀ a∈wires p,(run q mq s).basis a=s.basis a := by
    intro a ha
    apply run_preserves_outside
    exact fun hq => Finset.disjoint_left.mp hd ha hq
  have qRead : ∀ a∈wires q,(run p mp s).basis a=s.basis a := by
    intro a ha
    apply run_preserves_outside
    exact fun hp => Finset.disjoint_left.mp hd hp ha
  have hp := run_local_increment p (run q mq s) s mp pRead
  have hq := run_local_increment q (run p mp s) s mq qRead
  apply State.extensionality
  · exact phase_commutation _ _ _ _ _ hp.1 hq.1
  · funext a
    by_cases ha : a∈wires p
    · have away : a∉wires q := fun hh => Finset.disjoint_left.mp hd ha hh
      exact (hp.2 a ha).trans (run_preserves_outside q mq (run p mp s) a away).symm
    · rw [run_preserves_outside p mp (run q mq s) a ha]
      by_cases hb : a∈wires q
      · exact (hq.2 a hb).symm
      · rw [run_preserves_outside q mq (run p mp s) a hb,
          run_preserves_outside q mq s a hb,
          run_preserves_outside p mp s a ha]

end ECDSAAdd.Arithmetic
