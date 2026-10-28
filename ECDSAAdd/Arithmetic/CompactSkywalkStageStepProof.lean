import ECDSAAdd.Arithmetic.CompactSkywalkStageStepTails

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Actual compact physical stage advancement. Every old tape/work/fresh
field is transported, while both next full-word tails are proved clean. -/
theorem compactSkywalkStageStep (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1)
    (hp : p < 2^256) (hx : x < p) (hc : x.Coprime p) (hi : i < 512) :
    Triple (CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i)
      (compactSkywalkTick w i)
      (CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) (i+1)) := by
  intro s m hin
  let r := SkywalkRails.encode false false (x:Int) (p:Int)
  let ri := SkywalkTrace.next^[i] r
  let t := SkywalkRails.step ri
  let out := run (compactSkywalkTick w i) m s
  have fields := (compactSkywalkStage_fields_iff w r i (by omega) hn s.basis).mp hin
  rcases fields with ⟨readA,readB,prev,past,future,carry,orient,cleanA,cleanB⟩
  have input := compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hx hc hi s hin
  have fit := narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp hx hc hi
  have result := compactSkywalkTickOutput_spec w i hi hn ri.a ri.b ri.g
    fit.1 fit.2.1 fit.2.2.1 fit.2.2.2.1 fit.2.2.2.2 s m input
  have ho : CompactSkywalkTickOutput w i ri.a ri.b ri.g out.basis := result.2
  have tails := compactSkywalkStageStep_clean_tails w i hi hn r s m
    ⟨readA,readB,prev,past,future,carry,orient,cleanA,cleanB⟩ ri.a ri.b ri.g ho
  have views := compactSkywalkStageStep_retained w i hi
  have hnext : SkywalkTrace.next^[i+1] r = SkywalkRails.railsOf t := by
    rw [Function.iterate_succ_apply']
    rfl
  refine ⟨result.1,(compactSkywalkStage_fields_iff w r (i+1) (by omega) hn out.basis).mpr ?_⟩
  change CompactSkywalkStageFields w r (i+1) out.basis
  unfold CompactSkywalkStageFields
  rw [hnext]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,tails.1,tails.2⟩
  · rw [views.1]
    exact ho.1
  · rw [views.2]
    exact ho.2.1
  · change out.basis (w (skywalkPoolPreviousId (i+1))) = t.g
    rw [skywalkPoolPreviousId,if_neg (by omega : i+1 ≠ 0)]
    simpa only [Nat.add_sub_cancel] using ho.2.2.1
  · intro j hj
    by_cases now : j = i
    · subst j
      exact ⟨ho.2.2.1,ho.2.2.2.1⟩
    · have old : j < i := by omega
      have history := past j old
      have keepG : out.basis (w j) = s.basis (w j) := by
        by_cases last : j+1 = i
        · have hkeep := compactSkywalkStageMetadata_previousG w i (by omega)
            ri.a ri.b ri.g s.basis out.basis input ho
          have he : i-1 = j := by omega
          simpa only [he] using hkeep
        · exact compactSkywalkStageMetadata_pastG w i hi hn j (by omega) s m
      have keepS := compactSkywalkStageMetadata_pastS w i hi hn j old s m
      exact ⟨keepG.trans history.1,keepS.trans history.2⟩
  · intro j hj hj512
    have before := future j (by omega) hj512
    exact ⟨(compactSkywalkStageMetadata_futureExtension w i hi hn j hj hj512 s m).trans before.1,
      (compactSkywalkStageMetadata_futureS w i hi hn j hj hj512 s m).trans before.2⟩
  · apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    by_cases used : j < 1540+(compactSkywalkTickPreWidth i-1)
    · have carryClean := (regValue_zero _ _).mp ho.2.2.2.2.2.1
      apply carryClean
      change w j ∈ wireBlock w 1540 (compactSkywalkTickPreWidth i-1)
      exact List.mem_map.mpr ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩
    · have keep := compactSkywalkStageMetadata_carryTail w i hi hn j (by omega) (by omega) s m
      apply keep.trans
      exact (regValue_zero _ _).mp carry (w j)
        (List.mem_map.mpr ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩)
  · by_cases zero : i = 0
    · subst i
      exact (compactSkywalkStageMetadata_orientation_zero w ri.a ri.b ri.g
        s.basis out.basis input ho).trans orient
    · exact (compactSkywalkStageMetadata_orientation w i hi hn (by omega) s m).trans orient

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStageStep
