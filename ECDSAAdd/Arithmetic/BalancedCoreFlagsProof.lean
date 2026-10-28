import ECDSAAdd.Arithmetic.BalancedCoreLayoutProof
import ECDSAAdd.Framework.WireRename

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField

theorem seedViews_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hg : s.basis L.sourceGuard=false)
    (ho : s.basis L.one=false) (hp : s.basis L.parity=false) :
    run (seedViews L) m s=⟨s.phase,writeBit (writeBit (writeBit s.basis L.sourceGuard
      (s.basis L.ymsb)) L.one (s.basis L.rmsb)) L.parity
      (s.basis (L.ylow.getD 0 0) ^^ s.basis L.r0)⟩ := by
  have nd := seedND L hw hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6⟩,⟨h2_3,h2_4,h2_5,h2_6⟩,⟨h3_4,h3_5,h3_6⟩,⟨h4_5,h4_6⟩,h5_6⟩
  have h0_1r := Ne.symm h0_1
  have h0_2r := Ne.symm h0_2
  have h0_3r := Ne.symm h0_3
  have h0_4r := Ne.symm h0_4
  have h0_5r := Ne.symm h0_5
  have h0_6r := Ne.symm h0_6
  have h1_2r := Ne.symm h1_2
  have h1_3r := Ne.symm h1_3
  have h1_4r := Ne.symm h1_4
  have h1_5r := Ne.symm h1_5
  have h1_6r := Ne.symm h1_6
  have h2_3r := Ne.symm h2_3
  have h2_4r := Ne.symm h2_4
  have h2_5r := Ne.symm h2_5
  have h2_6r := Ne.symm h2_6
  have h3_4r := Ne.symm h3_4
  have h3_5r := Ne.symm h3_5
  have h3_6r := Ne.symm h3_6
  have h4_5r := Ne.symm h4_5
  have h4_6r := Ne.symm h4_6
  have h5_6r := Ne.symm h5_6
  simp only [seedViews,run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hqg : q=L.sourceGuard <;> by_cases hqo : q=L.one <;> by_cases hqp : q=L.parity <;>
    simp_all [writeBit,Function.update]

theorem prepareFold_run (L : Layout) (hn : L.wires.Nodup) (P N : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (ho : s.basis L.one=N)
    (hr : s.basis L.r0=P) (hl : s.basis L.lower=false)
    (hm : s.basis L.minus=false) (hu : s.basis L.plus=false) :
    run (prepareFold L) m s=⟨s.phase,
      writeBit (writeBit (writeBit (writeBit (writeBit s.basis L.lower N)
        L.minus (P && N)) L.plus (P && !N)) L.one (N ^^ P)) L.r0 false⟩ := by
  have nd : [L.one,L.parity,L.r0,L.lower,L.minus,L.plus].Nodup := by
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
  cases P <;> cases N
  all_goals
    simp only [prepareFold,run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hql : q=L.lower <;> by_cases hqm : q=L.minus <;> by_cases hqu : q=L.plus <;>
      by_cases hqo : q=L.one <;> by_cases hqr : q=L.r0 <;>
      simp_all [writeBit,Function.update]

/-- The remaining minus selector is P AND NOT(result sign). Its immediate
Z/CZ correction supplies the exact measured phase for either outcome. -/
theorem releaseSelectors_run (L : Layout) (hn : L.wires.Nodup) (P H : Bool)
    (s : State) (m : List Bool) (hp : s.basis L.parity=P) (hh : s.basis L.rmsb=H)
    (hl : s.basis L.lower=(H ^^ P)) (hm : s.basis L.minus=(P && !H))
    (hu : s.basis L.plus=(P ^^ (P && !H))) :
    run (releaseSelectors L) m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.lower false) L.plus false) L.minus false⟩ := by
  have nd : [L.parity,L.rmsb,L.lower,L.plus,L.minus].Nodup := by
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
  cases P <;> cases H <;> cases hr : m.headD false
  all_goals
    apply State.extensionality
    · simp_all [releaseSelectors,run,measureAndCorrect,correct,writeBit,Function.update]
    · funext q
      by_cases hql : q=L.lower <;> by_cases hqm : q=L.minus <;> by_cases hqu : q=L.plus <;>
        simp_all [releaseSelectors,run,measureAndCorrect,correct,writeBit,Function.update]

end ECDSAAdd.Arithmetic.BalancedCircuit

#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.releaseSelectors_run
