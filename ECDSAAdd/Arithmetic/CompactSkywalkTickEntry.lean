import ECDSAAdd.Arithmetic.CompactSkywalkTickProof
import ECDSAAdd.Arithmetic.CompactSkywalkSignReleasePair

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem block_prefix (w : Nat → Wire) (start len n : Nat) (hn : n ≤ len) :
    (wireBlock w start len).take n=wireBlock w start n := by
  have h := wireBlock_append w start n (len-n)
  have e : n+(len-n)=len := by omega
  rw [e] at h
  rw [←h]
  have take : (wireBlock w start n ++ wireBlock w (start+n) (len-n)).take
      (wireBlock w start n).length = wireBlock w start n := List.take_left
  simpa only [wireBlock_length] using take

private theorem entry_views (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkSignPoolA w i).retained=(compactSkywalkTickLayout w i).a ∧
    (compactSkywalkSignPoolB w i).retained=(compactSkywalkTickLayout w i).b := by
  have hw := compactSkywalkTick_width_bounds i hi
  have na : narrowSkywalkRouteWidth i ≤ (skywalkPoolA w i).length := by
    simpa only [skywalkPoolA,wireBlock_length] using hw.2.2.2.1
  have nb : narrowSkywalkRouteWidth i ≤ (skywalkPoolB w).length := by
    simpa only [skywalkPoolB,wireBlock_length] using hw.2.2.2.1
  have hpos : 0 < narrowSkywalkRouteWidth i := by
    change 0 < compactSkywalkTickPreWidth i
    omega
  have va := compactSkywalkSignWord_retained (skywalkPoolA w i) (narrowSkywalkRouteWidth i)
    hpos na
  have vb := compactSkywalkSignWord_retained (skywalkPoolB w) (narrowSkywalkRouteWidth i)
    hpos nb
  constructor
  · change (compactSkywalkSignWord (skywalkPoolA w i) (narrowSkywalkRouteWidth i)).retained=_
    rw [va,skywalkPoolA,compactSkywalkTick_a w i hi]
    exact block_prefix w i 258 _ hw.2.2.2.1
  · change (compactSkywalkSignWord (skywalkPoolB w) (narrowSkywalkRouteWidth i)).retained=_
    rw [vb,skywalkPoolB,compactSkywalkTick_b w i hi]
    exact block_prefix w 770 258 _ hw.2.2.2.1

private theorem index_away (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i < 512) (hj : j < 1798)
    (ha : j < i ∨ i+258 ≤ j) (hb : j < 770 ∨ 1028 ≤ j) :
    w j∉skywalkPoolA w i ∧ w j∉skywalkPoolB w := by
  constructor <;> intro hq
  · obtain ⟨k,hk,he⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hk
    have e := skywalkPool_index_inj w hn k j (by omega) hj he
    omega
  · obtain ⟨k,hk,he⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hk
    have e := skywalkPool_index_inj w hn k j (by omega) hj he
    omega

private theorem extension_in_release (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hsmall : compactSkywalkTickPreWidth i < 258) :
    w (i+compactSkywalkTickPreWidth i)∈(compactSkywalkSignPoolA w i).released := by
  have hw := compactSkywalkTick_width_bounds i hi
  change w (i+compactSkywalkTickPreWidth i)∈
    (wireBlock w i 258).drop (compactSkywalkTickPreWidth i)
  have h := wireBlock_append w i (compactSkywalkTickPreWidth i)
    (258-compactSkywalkTickPreWidth i)
  rw [show compactSkywalkTickPreWidth i+(258-compactSkywalkTickPreWidth i)=258 by omega] at h
  rw [←h]
  have drop : (wireBlock w i (compactSkywalkTickPreWidth i) ++
      wireBlock w (i+compactSkywalkTickPreWidth i) (258-compactSkywalkTickPreWidth i)).drop
      (wireBlock w i (compactSkywalkTickPreWidth i)).length =
      wireBlock w (i+compactSkywalkTickPreWidth i) (258-compactSkywalkTickPreWidth i) := List.drop_left
  simp only [wireBlock_length] at drop
  rw [drop]
  apply List.mem_map.mpr
  exact ⟨i+compactSkywalkTickPreWidth i,by simp only [List.mem_range'_1]; omega,rfl⟩

/-- Every zero required by the local tick comes from actual release or
the old fresh-extension/work frame. There is no new clean-work oracle. -/
theorem compactSkywalkTickEntry_from_stage (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p i : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (hi : i < 512) (s : State) (m : List Bool)
    (hin : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
    let t := run (compactSkywalkSignPoolRelease w i) m s
    t.phase=s.phase ∧ SkywalkIntegerInput (compactSkywalkTickLayout w i) r.a r.b r.g t.basis := by
  dsimp only
  generalize ht : run (compactSkywalkSignPoolRelease w i) m s=t
  have copies := compactSkywalkSignPool_stage_copies w x p i hp0 hx0 hpo hp hx hc hi s.basis hin
  have release := compactSkywalkSignPool_release_correct w i hi hn s m copies.1 copies.2
  rw [ht] at release
  obtain ⟨phase,cleanA,cleanB,valA,valB,frame⟩ := release
  have views := entry_views w i hi
  rw [views.1] at valA
  rw [views.2] at valB
  have keep (j : Nat) (hj : j < 1798) (ha : j < i ∨ i+258 ≤ j)
      (hb : j < 770 ∨ 1028 ≤ j) : t.basis (w j)=s.basis (w j) := by
    have away := index_away w hn i j hi hj ha hb
    exact frame _ away.1 away.2
  have prev := keep (skywalkPoolPreviousId i) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega) (by
    unfold skywalkPoolPreviousId; split_ifs <;> omega)
  have fresh := hin.2.2.2.2.1 i (Nat.le_refl i) hi
  refine ⟨phase,valA.trans hin.1,valB.trans hin.2.1,?_,?_,?_,?_⟩
  · change t.basis (w (skywalkPoolPreviousId i))=_
    exact prev.trans hin.2.2.1
  · change t.basis (w (i+compactSkywalkTickPreWidth i))=false
    have width := (compactSkywalkTick_width_bounds i hi).2.2.2.1
    by_cases hfull : compactSkywalkTickPreWidth i=258
    · rw [hfull,keep (i+258) (by omega) (by omega) (by omega)]
      exact fresh.1
    · exact cleanA _ (extension_in_release w i hi (by omega))
  · change t.basis (w (1028+i))=false
    exact (keep (1028+i) (by omega) (by omega) (by omega)).trans fresh.2
  · apply (regValue_zero _ _).mpr
    intro q hq
    change q∈wireBlock w 1540 (compactSkywalkTickPreWidth i-1) at hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have width := (compactSkywalkTick_width_bounds i hi).2.2.2.1
    have before := (regValue_zero _ _).mp hin.2.2.2.2.2.1 (w j) (by
      apply List.mem_map.mpr
      exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩)
    exact (keep j (by omega) (by omega) (by omega)).trans before

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTickEntry_from_stage
