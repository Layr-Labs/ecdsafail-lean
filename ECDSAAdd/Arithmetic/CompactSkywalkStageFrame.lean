import ECDSAAdd.Arithmetic.CompactSkywalkStageVirtual

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private theorem block_away (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start len j : Nat) (hb : start+len ≤ 1798) (hj : j < 1798)
    (ha : j < start ∨ start+len ≤ j) : w j ∉ wireBlock w start len := by
  intro hm
  obtain ⟨k,hk,he⟩ := List.mem_map.mp hm
  simp only [List.mem_range'_1] at hk
  have e := skywalkPool_index_inj w hn k j (by omega) hj he
  omega

/-- Raw tape, future extension sites and the complete carry bank are not
changed by mathematical sign reconstruction. -/
theorem compactSkywalkStage_virtual_index (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) (s : BasisState) (j : Nat) (hj : j < 1798)
    (ha : j < i ∨ i+258 ≤ j) (hb : j < 770 ∨ 1028 ≤ j) :
    compactSkywalkStageVirtual w i s (w j) = s (w j) := by
  have ea := compactSkywalkStage_expanded w i hi
  apply compactSkywalkStage_virtual_outside
  · intro hm
    have hw : w j ∈ skywalkPoolA w i := by rw [←ea.1]; exact List.mem_append_right _ hm
    exact block_away w hn i 258 j (by omega) hj ha hw
  · intro hm
    have hw : w j ∈ skywalkPoolB w := by rw [←ea.2]; exact List.mem_append_right _ hm
    exact block_away w hn 770 258 j (by decide) hj hb hw

/-- An index interval exclusion checks the actual local native/cleanup support. -/
theorem compactSkywalkStage_tick_away (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj : j < 1798)
    (hp : j ≠ skywalkPoolPreviousId i) (hh : j ≠ 1028+i)
    (he : j ≠ i+compactSkywalkTickPreWidth i) (hi0 : j ≠ i) (hb0 : j ≠ 770)
    (ha : j < i+1 ∨ i+compactSkywalkTickPreWidth i ≤ j)
    (hb : j < 771 ∨ 770+compactSkywalkTickPreWidth i ≤ j)
    (hc : j < 1540 ∨ 1540+(compactSkywalkTickPreWidth i-1) ≤ j) :
    w j ∉ (compactSkywalkTickLayout w i).wires := by
  have width := compactSkywalkTick_width_bounds i hi
  have distinct (k : Nat) (hk : k < 1798) (hne : j ≠ k) : w j ≠ w k := by
    intro e
    exact hne (skywalkPool_index_inj w hn j k hj hk e)
  have pa := distinct _ (by unfold skywalkPoolPreviousId; split_ifs <;> omega) hp
  have ph := distinct _ (by omega) hh
  have pe := distinct _ (by omega) he
  have pi := distinct _ (by omega) hi0
  have pb := distinct _ (by decide) hb0
  have aa := block_away w hn (i+1) (compactSkywalkTickPreWidth i-1) j (by omega) hj (by omega)
  have ab := block_away w hn 771 (compactSkywalkTickPreWidth i-1) j (by omega) hj (by omega)
  have ac := block_away w hn 1540 (compactSkywalkTickPreWidth i-1) j (by omega) hj hc
  simp only [SkywalkIntegerLayout.wires,compactSkywalkTick_ah w i hi,
    compactSkywalkTick_bh w i hi,List.mem_cons,List.mem_append]
  simp only [compactSkywalkTickLayout]
  tauto

theorem compactSkywalkStage_tick_keep (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (j : Nat) (hj : j < 1798)
    (hp : j ≠ skywalkPoolPreviousId i) (hh : j ≠ 1028+i)
    (he : j ≠ i+compactSkywalkTickPreWidth i) (hi0 : j ≠ i) (hb0 : j ≠ 770)
    (ha : j < i+1 ∨ i+compactSkywalkTickPreWidth i ≤ j)
    (hb : j < 771 ∨ 770+compactSkywalkTickPreWidth i ≤ j)
    (hc : j < 1540 ∨ 1540+(compactSkywalkTickPreWidth i-1) ≤ j)
    (s : State) (m : List Bool) :
    (run (compactSkywalkTick w i) m s).basis (w j) = s.basis (w j) :=
  compactSkywalkTickOutput_frame w i hi hn s m _
    (compactSkywalkStage_tick_away w i hi hn j hj hp hh he hi0 hb0 ha hb hc)

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStage_virtual_index
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStage_tick_keep
