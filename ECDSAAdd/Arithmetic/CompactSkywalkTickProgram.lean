import ECDSAAdd.Arithmetic.CompactSkywalkTickValidation

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

def compactSkywalkTickARelease (w : Nat → Wire) (i : Nat) : CompactSkywalkSignReleaseLayout :=
  compactSkywalkSignWord (compactSkywalkTickLayout w i).half (compactSkywalkTickPostWidth i)
def compactSkywalkTickBRelease (w : Nat → Wire) (i : Nat) : CompactSkywalkSignReleaseLayout :=
  compactSkywalkSignWord (compactSkywalkTickLayout w i).b (compactSkywalkTickPostWidth i)
def compactSkywalkTickCleanup (w : Nat → Wire) (i : Nat) : Program :=
  compactSkywalkSignRelease (compactSkywalkTickARelease w i)++
    compactSkywalkSignRelease (compactSkywalkTickBRelease w i)

/-- Actual compact route/record on local prefixes, followed only by CX release
of the post-boundary sign tails. No full258 reconstruction is emitted. -/
def compactSkywalkTick (w : Nat → Wire) (i : Nat) : Program :=
  narrowSkywalkTick (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)++
    compactSkywalkTickCleanup w i

attribute [local irreducible] narrowSkywalkTick compactSkywalkSignRelease

private theorem recordWordsND (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.half.Nodup ∧ L.b.Nodup ∧ L.half.Disjoint L.b := by
  have h := (List.nodup_cons.mp (L.record_nodup hv)).2
  exact List.nodup_append'.mp (List.nodup_append'.mp h).1

theorem compactSkywalkTick_release_valid (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    (compactSkywalkTickARelease w i).Valid ∧ (compactSkywalkTickBRelease w i).Valid := by
  have h := compactSkywalkTick_width_bounds i hi
  have nd := recordWordsND _ (compactSkywalkTick_valid w i hi hn)
  refine ⟨compactSkywalkSignWord_valid _ _ (by omega) ?_ nd.1,
    compactSkywalkSignWord_valid _ _ (by omega) ?_ nd.2.1⟩
  · rw [compactSkywalkTick_half w i hi,wireBlock_length]
    exact h.2.2.1
  · rw [compactSkywalkTick_b w i hi,wireBlock_length]
    exact h.2.2.1

theorem compactSkywalkTick_words_disjoint (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    (compactSkywalkTickLayout w i).half.Disjoint (compactSkywalkTickLayout w i).b :=
  (recordWordsND _ (compactSkywalkTick_valid w i hi hn)).2.2

theorem compactSkywalkTick_cleanup_counts (w : Nat → Wire) (i : Nat) :
    toffoliCount (compactSkywalkTickCleanup w i) = 0 ∧
    measurementCount (compactSkywalkTickCleanup w i) = 0 := by
  have a := compactSkywalkSignRelease_counts (compactSkywalkTickARelease w i)
  have b := compactSkywalkSignRelease_counts (compactSkywalkTickBRelease w i)
  rw [compactSkywalkTickCleanup,toffoliCount_append,measurementCount_append,a.1,a.2.1,b.1,b.2.1]
  exact ⟨rfl,rfl⟩

theorem compactSkywalkTick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (compactSkywalkTick w i) =
      (compactSkywalkTickPreWidth i-1)+(compactSkywalkTickPostWidth i-1) ∧
    measurementCount (compactSkywalkTick w i) = compactSkywalkTickPostWidth i-1 := by
  have h := compactSkywalkTick_width_bounds i hi
  have len : (compactSkywalkTickLayout w i).half.length = compactSkywalkTickPreWidth i := by
    rw [compactSkywalkTick_half w i hi,wireBlock_length]
  have c := narrowSkywalkTick_counts _ (compactSkywalkTick_valid w i hi hn)
    (compactSkywalkTickPostWidth i) (by omega) (by rw [len]; exact h.2.2.1)
  have z := compactSkywalkTick_cleanup_counts w i
  rw [compactSkywalkTick,toffoliCount_append,measurementCount_append,c.1,c.2.1,z.1,z.2]
  rw [compactSkywalkTick_ah w i hi,wireBlock_length]
  exact ⟨by omega,by omega⟩

theorem compactSkywalkTick_cleanup_support (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    wires (compactSkywalkTickCleanup w i) ⊆ (compactSkywalkTickLayout w i).wires.toFinset := by
  have h := compactSkywalkTick_width_bounds i hi
  have a := (compactSkywalkSignWord_support (compactSkywalkTickLayout w i).half
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)).1
  have b := (compactSkywalkSignWord_support (compactSkywalkTickLayout w i).b
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_b w i hi,wireBlock_length]; exact h.2.2.1)).1
  intro q hq
  simp only [compactSkywalkTickCleanup,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · have ha := List.mem_toFinset.mp (a hq)
    simp only [SkywalkIntegerLayout.half,SkywalkIntegerLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
    tauto
  · have hb := List.mem_toFinset.mp (b hq)
    simp only [SkywalkIntegerLayout.b,SkywalkIntegerLayout.wires,List.mem_toFinset,
      List.mem_append,List.mem_cons] at hb ⊢
    tauto

theorem compactSkywalkTick_support (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) :
    wires (compactSkywalkTick w i) ⊆ (compactSkywalkTickLayout w i).wires.toFinset := by
  have h := compactSkywalkTick_width_bounds i hi
  have n := (narrowSkywalkTick_wires_subset _ (compactSkywalkTick_valid w i hi hn)
    (compactSkywalkTickPostWidth i) (by omega) (by
      rw [compactSkywalkTick_half w i hi,wireBlock_length]; exact h.2.2.1)).1
  have c := compactSkywalkTick_cleanup_support w i hi
  rw [compactSkywalkTick,wires_append,Finset.union_subset_iff]
  exact ⟨n,c⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTick_counts
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTick_support
