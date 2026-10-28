import ECDSAAdd.Arithmetic.CompactSkywalkSignReleasePool

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem word_subviews (r : List Wire) (n : Nat) (hn : 0 < n) (hle : n ≤ r.length) :
    (compactSkywalkSignWord r n).retained⊆r ∧
    (compactSkywalkSignWord r n).released⊆r ∧ (compactSkywalkSignWord r n).sign ∈ r := by
  have he := compactSkywalkSignWord_expanded r n hn hle
  refine ⟨?_,?_,?_⟩
  · intro q hq
    rw [←he]
    exact List.mem_append_left _ hq
  · intro q hq
    rw [←he]
    exact List.mem_append_right _ hq
  · have hs : (compactSkywalkSignWord r n).sign ∈ (compactSkywalkSignWord r n).retained := by
      simp [CompactSkywalkSignReleaseLayout.retained]
    have hx : (compactSkywalkSignWord r n).sign ∈ (compactSkywalkSignWord r n).expanded :=
      List.mem_append_left _ hs
    simpa only [he] using hx

private theorem same_signed (r : List Wire) (s t : BasisState)
    (he : ∀q ∈ r,t q = s q) : signedRegValue r t = signedRegValue r s := by
  unfold signedRegValue
  rw [regValue_congr r t s he]

/-- The emitted two-bank release really frees both physical tails, preserves
both exact signed prefix values and every outsider, and changes no phase. -/
theorem compactSkywalkSignPool_release_correct (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (hcA : (compactSkywalkSignPoolA w i).Copies s.basis)
    (hcB : (compactSkywalkSignPoolB w i).Copies s.basis) :
    (run (compactSkywalkSignPoolRelease w i) m s).phase = s.phase ∧
    (compactSkywalkSignPoolA w i).Clean (run (compactSkywalkSignPoolRelease w i) m s).basis ∧
    (compactSkywalkSignPoolB w i).Clean (run (compactSkywalkSignPoolRelease w i) m s).basis ∧
    signedRegValue (compactSkywalkSignPoolA w i).retained
      (run (compactSkywalkSignPoolRelease w i) m s).basis = signedRegValue (skywalkPoolA w i) s.basis ∧
    signedRegValue (compactSkywalkSignPoolB w i).retained
      (run (compactSkywalkSignPoolRelease w i) m s).basis = signedRegValue (skywalkPoolB w) s.basis ∧
    (∀q,q ∉ skywalkPoolA w i → q ∉ skywalkPoolB w →
      (run (compactSkywalkSignPoolRelease w i) m s).basis q = s.basis q) := by
  let A := compactSkywalkSignPoolA w i
  let B := compactSkywalkSignPoolB w i
  let u := run (compactSkywalkSignRelease A) m s
  let v := run (compactSkywalkSignRelease B) m u
  have hv := compactSkywalkSignPool_valid w i hi hn
  have hw := narrowSkywalkRouteWidth_bounds i hi
  have la : narrowSkywalkRouteWidth i ≤ (skywalkPoolA w i).length := by
    simpa [skywalkPoolA,wireBlock] using hw.2.1
  have lb : narrowSkywalkRouteWidth i ≤ (skywalkPoolB w).length := by
    simpa [skywalkPoolB,wireBlock] using hw.2.1
  have av := word_subviews (skywalkPoolA w i) (narrowSkywalkRouteWidth i) (by omega) la
  have bv := word_subviews (skywalkPoolB w) (narrowSkywalkRouteWidth i) (by omega) lb
  have sa := (compactSkywalkSignWord_support (skywalkPoolA w i)
    (narrowSkywalkRouteWidth i) (by omega) la).1
  have sb := (compactSkywalkSignWord_support (skywalkPoolB w)
    (narrowSkywalkRouteWidth i) (by omega) lb).1
  have hd := compactSkywalkSignPool_wordsDisjoint w i hi hn
  have ub : ∀q ∈ skywalkPoolB w,u.basis q = s.basis q := by
    intro q hq
    exact run_preserves_outside _ m s q (fun hs =>
      List.disjoint_left.mp hd (List.mem_toFinset.mp (sa hs)) hq)
  have va : ∀q ∈ skywalkPoolA w i,v.basis q = u.basis q := by
    intro q hq
    exact run_preserves_outside _ m u q (fun hs =>
      List.disjoint_left.mp hd hq (List.mem_toFinset.mp (sb hs)))
  have uCopiesB : B.Copies u.basis := by
    intro q hq
    rw [ub q (bv.2.1 hq),ub B.sign bv.2.2]
    exact hcB q hq
  have uCleanA := compactSkywalkSignRelease_clean A hv.1 s m hcA
  have vCleanA : A.Clean v.basis := by
    intro q hq
    exact (va q (av.2.1 hq)).trans (uCleanA q hq)
  have vCleanB := compactSkywalkSignRelease_clean B hv.2 u m uCopiesB
  have aValue := (same_signed A.retained u.basis v.basis
    (fun q hq => va q (av.1 hq))).trans
      (compactSkywalkSignRelease_signed A hv.1 s m hcA)
  have bValue := (compactSkywalkSignRelease_signed B hv.2 u m uCopiesB).trans
    (same_signed B.expanded s.basis u.basis (by
      intro q hq
      have he := compactSkywalkSignWord_expanded (skywalkPoolB w)
        (narrowSkywalkRouteWidth i) (by omega) lb
      change q ∈ (compactSkywalkSignWord (skywalkPoolB w) (narrowSkywalkRouteWidth i)).expanded at hq
      rw [he] at hq
      exact ub q hq))
  have ar : A.expanded = skywalkPoolA w i := compactSkywalkSignWord_expanded _ _ (by omega) la
  have br : B.expanded = skywalkPoolB w := compactSkywalkSignWord_expanded _ _ (by omega) lb
  rw [ar] at aValue
  rw [br] at bValue
  have ca := compactSkywalkSignRelease_counts A
  have actual : run (compactSkywalkSignPoolRelease w i) m s = v :=
    compactSkywalkSign_no_measure_append _ _ ca.2.1 s m
  rw [actual]
  have pa := (compactSkywalkSignRelease_phase_frame A hv.1 s m).1
  have pb := (compactSkywalkSignRelease_phase_frame B hv.2 u m).1
  refine ⟨pb.trans pa,vCleanA,vCleanB,aValue,bValue,?_⟩
  intro q hqa hqb
  have ua := run_preserves_outside (compactSkywalkSignRelease A) m s q
    (fun h => hqa (List.mem_toFinset.mp (sa h)))
  exact (run_preserves_outside (compactSkywalkSignRelease B) m u q
    (fun h => hqb (List.mem_toFinset.mp (sb h)))).trans ua

/-- Every valid complete logical trajectory therefore has an actual clean
physical release boundary at the universally proved width N_i. -/
theorem compactSkywalkSignPool_stage_release (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p i : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (hi : i < 512) (s : State) (m : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    (compactSkywalkSignPoolA w i).Clean (run (compactSkywalkSignPoolRelease w i) m s).basis ∧
    (compactSkywalkSignPoolB w i).Clean (run (compactSkywalkSignPoolRelease w i) m s).basis ∧
    signedRegValue (compactSkywalkSignPoolA w i).retained
      (run (compactSkywalkSignPoolRelease w i) m s).basis = 
        (SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))).a ∧
    signedRegValue (compactSkywalkSignPoolB w i).retained
      (run (compactSkywalkSignPoolRelease w i) m s).basis = 
        (SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))).b := by
  have copies := compactSkywalkSignPool_stage_copies w x p i hp0 hx0 hpo hp hx hc hi s.basis hin
  have h := compactSkywalkSignPool_release_correct w i hi hn s m copies.1 copies.2
  exact ⟨h.2.1,h.2.2.1,h.2.2.2.1.trans hin.1,h.2.2.2.2.1.trans hin.2.1⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignPool_release_correct
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignPool_stage_release
