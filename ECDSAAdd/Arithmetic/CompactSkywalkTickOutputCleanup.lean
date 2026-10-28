import ECDSAAdd.Arithmetic.CompactSkywalkTickProof
import ECDSAAdd.Arithmetic.CompactSkywalkSignReleasePool

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem subviews (r : List Wire) (n : Nat) (hn : 0 < n) (hle : n ≤ r.length) :
    (compactSkywalkSignWord r n).retained ⊆ r ∧
    (compactSkywalkSignWord r n).released ⊆ r ∧ (compactSkywalkSignWord r n).sign ∈ r := by
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

/-- These are actual two-bank CX instructions, with both clean tails and
retained signed values proved from the native result's sign-copy predicates. -/
theorem compactSkywalkTickOutput_cleanup_correct (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (s : State) (m : List Bool)
    (hcA : (compactSkywalkTickARelease w i).Copies s.basis)
    (hcB : (compactSkywalkTickBRelease w i).Copies s.basis) :
    (run (compactSkywalkTickCleanup w i) m s).phase = s.phase ∧
    (compactSkywalkTickARelease w i).Clean (run (compactSkywalkTickCleanup w i) m s).basis ∧
    (compactSkywalkTickBRelease w i).Clean (run (compactSkywalkTickCleanup w i) m s).basis ∧
    signedRegValue (compactSkywalkTickARelease w i).retained
      (run (compactSkywalkTickCleanup w i) m s).basis =
        signedRegValue (compactSkywalkTickLayout w i).half s.basis ∧
    signedRegValue (compactSkywalkTickBRelease w i).retained
      (run (compactSkywalkTickCleanup w i) m s).basis =
        signedRegValue (compactSkywalkTickLayout w i).b s.basis ∧
    (∀q,q ∉ (compactSkywalkTickLayout w i).half → q ∉ (compactSkywalkTickLayout w i).b →
      (run (compactSkywalkTickCleanup w i) m s).basis q = s.basis q) := by
  let L := compactSkywalkTickLayout w i
  let A := compactSkywalkTickARelease w i
  let B := compactSkywalkTickBRelease w i
  let u := run (compactSkywalkSignRelease A) m s
  let v := run (compactSkywalkSignRelease B) m u
  have hv := compactSkywalkTick_release_valid w i hi hn
  have hw := compactSkywalkTick_width_bounds i hi
  have la : compactSkywalkTickPostWidth i ≤ L.half.length := by
    rw [compactSkywalkTick_half w i hi,wireBlock_length]
    exact hw.2.2.1
  have lb : compactSkywalkTickPostWidth i ≤ L.b.length := by
    rw [compactSkywalkTick_b w i hi,wireBlock_length]
    exact hw.2.2.1
  have av := subviews L.half (compactSkywalkTickPostWidth i) (by omega) la
  have bv := subviews L.b (compactSkywalkTickPostWidth i) (by omega) lb
  have sa := (compactSkywalkSignWord_support L.half (compactSkywalkTickPostWidth i) (by omega) la).1
  have sb := (compactSkywalkSignWord_support L.b (compactSkywalkTickPostWidth i) (by omega) lb).1
  have hd := compactSkywalkTick_words_disjoint w i hi hn
  have ub : ∀q ∈ L.b,u.basis q = s.basis q := by
    intro q hq
    exact run_preserves_outside _ m s q (fun h =>
      List.disjoint_left.mp hd (List.mem_toFinset.mp (sa h)) hq)
  have va : ∀q ∈ L.half,v.basis q = u.basis q := by
    intro q hq
    exact run_preserves_outside _ m u q (fun h =>
      List.disjoint_left.mp hd hq (List.mem_toFinset.mp (sb h)))
  have uCopiesB : B.Copies u.basis := by
    intro q hq
    have keepQ : u.basis q = s.basis q := ub q (bv.2.1 hq)
    have keepS : u.basis B.sign = s.basis B.sign := ub B.sign bv.2.2
    rw [keepQ,keepS]
    exact hcB q hq
  have uCleanA := compactSkywalkSignRelease_clean A hv.1 s m hcA
  have vCleanA : A.Clean v.basis := by
    intro q hq
    exact (va q (av.2.1 hq)).trans (uCleanA q hq)
  have vCleanB := compactSkywalkSignRelease_clean B hv.2 u m uCopiesB
  have aValue := (same_signed A.retained u.basis v.basis
    (fun q hq => va q (av.1 hq))).trans (compactSkywalkSignRelease_signed A hv.1 s m hcA)
  have bValue := (compactSkywalkSignRelease_signed B hv.2 u m uCopiesB).trans
    (same_signed B.expanded s.basis u.basis (by
      intro q hq
      have he : B.expanded = L.b := compactSkywalkSignWord_expanded _ _ (by omega) lb
      rw [he] at hq
      exact ub q hq))
  have ar : A.expanded = L.half := compactSkywalkSignWord_expanded _ _ (by omega) la
  have br : B.expanded = L.b := compactSkywalkSignWord_expanded _ _ (by omega) lb
  rw [ar] at aValue
  rw [br] at bValue
  have ca := compactSkywalkSignRelease_counts A
  have actual : run (compactSkywalkTickCleanup w i) m s = v :=
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

/-- Orientation, sign-history, previous control and every local carry are
outside the two mutable words, by the physical local-layout distinctness. -/
theorem compactSkywalkTickOutput_metadataAway (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (q : Wire)
    (hq : q ∈ [(compactSkywalkTickLayout w i).a0,(compactSkywalkTickLayout w i).history,
      (compactSkywalkTickLayout w i).previous]++(compactSkywalkTickLayout w i).carry) :
    q ∉ (compactSkywalkTickLayout w i).half ∧ q ∉ (compactSkywalkTickLayout w i).b := by
  have h := List.nodup_iff_count.mp (compactSkywalkTick_valid w i hi hn).nodup q
  have hp := List.count_pos_iff.mpr hq
  constructor <;> intro hd <;> have hv := List.count_pos_iff.mpr hd
  all_goals
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,
      List.count_append,List.count_cons,List.count_nil] at h hp hv
    omega

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTickOutput_cleanup_correct
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTickOutput_metadataAway
