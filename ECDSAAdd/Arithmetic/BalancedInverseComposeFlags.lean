import ECDSAAdd.Arithmetic.BalancedFieldInverseParity
import ECDSAAdd.Arithmetic.BalancedFieldInverseArithmetic
import ECDSAAdd.Arithmetic.BalancedCoreFlagsProof
import ECDSAAdd.Arithmetic.BalancedCoreFoldProof

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

/-- Selector reconstruction is the actual six-gate stream. -/
theorem recoverSelectors_run (L : Layout) (hn : L.wires.Nodup) (P H : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P)
    (hh : s.basis L.rmsb=H) (hl : s.basis L.lower=false)
    (hm : s.basis L.minus=false) (hu : s.basis L.plus=false) :
    run (recoverSelectors L) m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.minus (P && !H))
        L.plus (P && H)) L.lower (H ^^ P)⟩ := by
  have nd : [L.parity,L.rmsb,L.lower,L.minus,L.plus].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4⟩,⟨h1_2,h1_3,h1_4⟩,⟨h2_3,h2_4⟩,h3_4⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h3_4r := Ne.symm h3_4
  cases P <;> cases H
  all_goals
    simp only [recoverSelectors,run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqm : q=L.minus <;> by_cases hqu : q=L.plus <;> by_cases hql : q=L.lower <;>
      simp_all [writeBit,Function.update]

/-- The inverse preparation uses a fresh X measurement with its CZ
correction; phase restoration holds for either record value. -/
theorem undoPreparation_run (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P)
    (ho : s.basis L.one=(N ^^ P)) (hr : s.basis L.r0=false)
    (hl : s.basis L.lower=N) (hm : s.basis L.minus=(P && N))
    (hu : s.basis L.plus=(P && !N)) :
    run (undoPreparation L) m s=⟨s.phase,
      writeBit (writeBit (writeBit (writeBit (writeBit s.basis L.r0 P)
        L.one N) L.plus false) L.minus false) L.lower false⟩ := by
  have nd : [L.parity,L.one,L.r0,L.lower,L.minus,L.plus].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5⟩,⟨h1_2,h1_3,h1_4,h1_5⟩,⟨h2_3,h2_4,h2_5⟩,⟨h3_4,h3_5⟩,h4_5⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h4_5r := Ne.symm h4_5
  cases P <;> cases N <;> cases hx : m.headD false
  all_goals
    apply State.extensionality
    · simp_all [undoPreparation,run,measureAndCorrect,correct,writeBit,Function.update]
    · funext q
      by_cases hqr : q=L.r0 <;> by_cases hqo : q=L.one <;>
        by_cases hqu : q=L.plus <;> by_cases hqm : q=L.minus <;> by_cases hql : q=L.lower <;>
        simp_all [undoPreparation,run,measureAndCorrect,correct,writeBit,Function.update]

/-- The recovered threshold flag is the exact oddness of the inverse raw sum. -/
theorem result_parity (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    decide (q < |2*R-signedY B Y|)=originalParity (rawSum B (result B R Y) Y) := by
  have h := halfResult_parity_interval B (result B R Y) Y (result_bounds B R Y) hy
  rw [result_half B R Y hr hy] at h
  exact (decide_eq_decide.mpr h).symm

/-- Original raw sign is reconstructed from result sign and original parity. -/
theorem result_sign (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y) :
    (decide (R<0) ^^ originalParity (rawSum B (result B R Y) Y))=
      decide (rawSum B (result B R Y) Y<0) := by
  have h := halfResult_sign (rawSum B (result B R Y) Y)
    (rawSum_bounds B _ Y (result_bounds B R Y) hy)
  rw [result_half B R Y hr hy] at h
  rw [h]
  cases decide (rawSum B (result B R Y) Y<0) <;>
    cases originalParity (rawSum B (result B R Y) Y) <;> rfl

end ECDSAAdd.Arithmetic.BalancedInverse

#print axioms ECDSAAdd.Arithmetic.BalancedInverse.recoverSelectors_run
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.undoPreparation_run
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.result_parity
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.result_sign
