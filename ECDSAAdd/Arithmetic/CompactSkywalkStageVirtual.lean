import ECDSAAdd.Arithmetic.CompactSkywalkStageViews

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem signed_congr (r : List Wire) (s t : BasisState)
    (he : ∀q∈r,s q=t q) : signedRegValue r s=signedRegValue r t := by
  unfold signedRegValue
  rw [regValue_congr r s t he]

private theorem parts (w : Nat → Wire) (i : Nat) (hi : i ≤ 512) :
    (compactSkywalkSignPoolA w i).released ⊆ skywalkPoolA w i ∧
    (compactSkywalkSignPoolB w i).released ⊆ skywalkPoolB w ∧
    (compactSkywalkSignPoolA w i).sign ∈ skywalkPoolA w i ∧
    (compactSkywalkSignPoolB w i).sign ∈ skywalkPoolB w := by
  have he := compactSkywalkStage_expanded w i hi
  refine ⟨?_,?_,?_,?_⟩
  · intro q hq; rw [←he.1]; exact List.mem_append_right _ hq
  · intro q hq; rw [←he.2]; exact List.mem_append_right _ hq
  · have hs : (compactSkywalkSignPoolA w i).sign ∈ (compactSkywalkSignPoolA w i).expanded :=
      List.mem_append_left _ (by simp [CompactSkywalkSignReleaseLayout.retained])
    simpa only [he.1] using hs
  · have hs : (compactSkywalkSignPoolB w i).sign ∈ (compactSkywalkSignPoolB w i).expanded :=
      List.mem_append_left _ (by simp [CompactSkywalkSignReleaseLayout.retained])
    simpa only [he.2] using hs

theorem compactSkywalkStage_virtual_signs (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) (s : BasisState) :
    compactSkywalkStageVirtual w i s (compactSkywalkSignPoolA w i).sign =
      s (compactSkywalkSignPoolA w i).sign ∧
    compactSkywalkStageVirtual w i s (compactSkywalkSignPoolB w i).sign =
      s (compactSkywalkSignPoolB w i).sign := by
  have hv := compactSkywalkStage_valid w i hi hn
  have hd := compactSkywalkStage_words_disjoint w i hi hn
  have hp := parts w i hi
  constructor
  · apply compactSkywalkStage_virtual_outside
    · exact (compactSkywalkSignPoolA w i).signAway hv.1
    · intro hq
      exact List.disjoint_left.mp hd hp.2.2.1 (hp.2.1 hq)
  · apply compactSkywalkStage_virtual_outside
    · intro hq
      exact List.disjoint_left.mp hd (hp.1 hq) hp.2.2.2
    · exact (compactSkywalkSignPoolB w i).signAway hv.2

theorem compactSkywalkStage_virtual_copies (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) (s : BasisState) :
    (compactSkywalkSignPoolA w i).Copies (compactSkywalkStageVirtual w i s) ∧
    (compactSkywalkSignPoolB w i).Copies (compactSkywalkStageVirtual w i s) := by
  have hs := compactSkywalkStage_virtual_signs w i hi hn s
  have hd := compactSkywalkStage_words_disjoint w i hi hn
  have hp := parts w i hi
  constructor
  · intro q hq
    rw [hs.1]
    simp [compactSkywalkStageVirtual,hq]
  · intro q hq
    have ha : q ∉ (compactSkywalkSignPoolA w i).released := by
      intro hm
      exact List.disjoint_left.mp hd (hp.1 hm) (hp.2.1 hq)
    rw [hs.2]
    simp [compactSkywalkStageVirtual,ha,hq]

/-- Virtual full reads are exactly the current physical retained signed reads. -/
theorem compactSkywalkStage_virtual_values (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) (s : BasisState) :
    signedRegValue (skywalkPoolA w i) (compactSkywalkStageVirtual w i s) =
      signedRegValue (compactSkywalkSignPoolA w i).retained s ∧
    signedRegValue (skywalkPoolB w) (compactSkywalkStageVirtual w i s) =
      signedRegValue (compactSkywalkSignPoolB w i).retained s := by
  have hv := compactSkywalkStage_valid w i hi hn
  have he := compactSkywalkStage_expanded w i hi
  have hd := compactSkywalkStage_words_disjoint w i hi hn
  have hp := parts w i hi
  constructor
  · rw [←he.1]
    apply Eq.trans (signed_congr _ _ _ ?_)
      (compactSkywalkSignRelease_virtual_signed _ hv.1 s)
    intro q hq
    have hb : q ∉ (compactSkywalkSignPoolB w i).released := by
      intro hm
      rw [he.1] at hq
      exact List.disjoint_left.mp hd hq (hp.2.1 hm)
    simp [compactSkywalkStageVirtual,CompactSkywalkSignReleaseLayout.reconstructed,hb]
  · rw [←he.2]
    apply Eq.trans (signed_congr _ _ _ ?_)
      (compactSkywalkSignRelease_virtual_signed _ hv.2 s)
    intro q hq
    have ha : q ∉ (compactSkywalkSignPoolA w i).released := by
      intro hm
      rw [he.2] at hq
      exact List.disjoint_left.mp hd (hp.1 hm) hq
    simp [compactSkywalkStageVirtual,CompactSkywalkSignReleaseLayout.reconstructed,ha]

/-- Mathematical reconstruction followed by ghost release is exactly the
physical state. This equivalence emits no expansion in the compact circuit. -/
theorem compactSkywalkStage_release_virtual (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (hcA : (compactSkywalkSignPoolA w i).Clean s.basis)
    (hcB : (compactSkywalkSignPoolB w i).Clean s.basis) :
    run (compactSkywalkSignPoolRelease w i) m
      ⟨s.phase,compactSkywalkStageVirtual w i s.basis⟩ = s := by
  let v : State := ⟨s.phase,compactSkywalkStageVirtual w i s.basis⟩
  let A := compactSkywalkSignPoolA w i
  let B := compactSkywalkSignPoolB w i
  let u := run (compactSkywalkSignRelease A) m v
  let t := run (compactSkywalkSignRelease B) m u
  have hv := compactSkywalkSignPool_valid w i hi hn
  have copies := compactSkywalkStage_virtual_copies w i (by omega) hn s.basis
  have h := compactSkywalkSignPool_release_correct w i hi hn v m copies.1 copies.2
  have ca := compactSkywalkSignRelease_counts A
  have actual : run (compactSkywalkSignPoolRelease w i) m v = t :=
    compactSkywalkSign_no_measure_append _ _ ca.2.1 v m
  rw [actual] at h
  change run (compactSkywalkSignPoolRelease w i) m v = s
  rw [actual]
  apply congrArg₂ State.mk
  · exact h.1
  · funext q
    by_cases ha : q ∈ A.released
    · exact (h.2.1 q ha).trans (hcA q ha).symm
    by_cases hb : q ∈ B.released
    · exact (h.2.2.1 q hb).trans (hcB q hb).symm
    have a := (compactSkywalkSignRelease_phase_frame A hv.1 v m).2.1 q ha
    have b := (compactSkywalkSignRelease_phase_frame B hv.2 u m).2.1 q hb
    exact (b.trans a).trans (compactSkywalkStage_virtual_outside w i s.basis q ha hb)

/-- Every local tick input is obtained from the compact-stage predicate by
verified ghost release. No extra clean extension or work oracle is introduced. -/
theorem compactSkywalkStage_local_input (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p i : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (hi : i < 512) (s : State)
    (hin : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
    SkywalkIntegerInput (compactSkywalkTickLayout w i) r.a r.b r.g s.basis := by
  have entry := compactSkywalkTickEntry_from_stage w hn x p i hp0 hx0 hpo hp hx hc hi
    ⟨s.phase,compactSkywalkStageVirtual w i s.basis⟩ [] hin.1
  have eq := compactSkywalkStage_release_virtual w i hi hn s [] hin.2.1 hin.2.2
  rw [eq] at entry
  exact entry.2

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStage_virtual_values
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStage_release_virtual
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStage_local_input
