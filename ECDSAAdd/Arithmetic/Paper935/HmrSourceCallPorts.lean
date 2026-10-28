import ECDSAAdd.Arithmetic.Paper935.HmrRowMulSpec

namespace ECDSAAdd.Arithmetic.Paper935

/-- Actual seam roles at source pin 64b5a13, engine.py:2907–2938 (singles_on/on); circuit.py:126,179.
The absent generic multiplier roles have no physical address. -/
structure HmrSeamPorts where
  flag : Wire
  anc : List Wire
  anc_length : anc.length = 24
  distinct : (flag :: anc).Nodup

def HmrSeamPorts.carry (_ : HmrSeamPorts) : Option Wire := none
def HmrSeamPorts.top (_ : HmrSeamPorts) : Option Wire := none
def HmrSeamPorts.tq (_ : HmrSeamPorts) : Option Wire := none
def HmrSeamPorts.clean3 (_ : HmrSeamPorts) : List Wire := []

def s2HmrSeamPorts : HmrSeamPorts := ⟨851, [836, 867, 840, 810, 837, 907, 841, 807, 825, 803, 834, 809, 824, 792, 805, 789, 819, 802, 832, 929, 826, 783, 847, 926], by decide +kernel, by decide +kernel⟩

def s2HmrSourceRow : WindowRow := ⟨(List.range' 4 252).reverse ++ [0, 1, 2, 3, 794, 778, 798, 822, 814, 816, 891, 797, 781, 791, 920, 845, 896, 918, 780, 903, 925, 796, 800, 820, 846, 782, 835, 799], 770⟩

def s2HmrSourceY : List Wire := List.range' 256 256
def s2HmrSourceOut : List Wire := List.range' 512 256

theorem s2HmrSourceRow_length : s2HmrSourceRow.payload.length = 280 := by simp [s2HmrSourceRow]

theorem s2HmrSeamPorts_foldCarry : s2HmrSeamPorts.anc[0]? = some 836 := rfl

def s6HmrSeamPorts : HmrSeamPorts := ⟨784, [794, 891, 853, 818, 850, 792, 867, 880, 821, 863, 841, 864, 814, 868, 823, 802, 888, 796, 848, 930, 869, 807, 922, 797], by decide +kernel, by decide +kernel⟩

def s6HmrSourceRow : WindowRow := ⟨(List.range' 4 252).reverse ++ [0, 1, 2, 3, 907, 768, 845, 838, 822, 780, 809, 908, 813, 779, 896, 855, 812, 808, 887, 906, 918, 858, 805, 886, 803, 862, 839, 890], 776⟩

def s6HmrSourceY : List Wire := List.range' 512 256
def s6HmrSourceOut : List Wire := List.range' 256 256

theorem s6HmrSourceRow_length : s6HmrSourceRow.payload.length = 280 := by simp [s6HmrSourceRow]

theorem s6HmrSeamPorts_foldCarry : s6HmrSeamPorts.anc[0]? = some 794 := rfl


/-- Source engine.py:3200–3246 allocates this temporary in _fold_stage.
Exported from all 498 halves/doubles; release requires a separate zero proof. -/
def s2HmrFoldTemporary : Wire := 804

def s2HmrSourceLayout : HmrRowMulLayout where
  row := s2HmrSourceRow
  y := s2HmrSourceY
  out := s2HmrSourceOut
  anc := s2HmrSeamPorts.anc
  flags := {s2HmrSeamPorts.flag, s2HmrFoldTemporary}
  row_length := s2HmrSourceRow_length
  y_length := by simp [s2HmrSourceY]
  out_length := by simp [s2HmrSourceOut]
  anc_length := s2HmrSeamPorts.anc_length
  distinct := by
    simp only [s2HmrSourceRow, s2HmrSourceY, s2HmrSourceOut,
      s2HmrSeamPorts, List.nodup_append, List.nodup_cons,
      List.nodup_reverse]
    all_goals simp [List.mem_range',
      List.nodup_range' (s := 4) (n := 252),
      List.nodup_range' (s := 256) (n := 256),
      List.nodup_range' (s := 512) (n := 256)]
    all_goals repeat' first | constructor | intro
    all_goals try dsimp [Wire] at *
    all_goals omega
  flags_separate := by
    simp [s2HmrSourceRow, s2HmrSourceY, s2HmrSourceOut,
      s2HmrSeamPorts, s2HmrFoldTemporary, List.mem_range']
    repeat' first | constructor | intro
    all_goals omega

/-- Source engine.py:3200–3246 allocates this temporary in _fold_stage.
Exported from all 498 halves/doubles; release requires a separate zero proof. -/
def s6HmrFoldTemporary : Wire := 856

def s6HmrSourceLayout : HmrRowMulLayout where
  row := s6HmrSourceRow
  y := s6HmrSourceY
  out := s6HmrSourceOut
  anc := s6HmrSeamPorts.anc
  flags := {s6HmrSeamPorts.flag, s6HmrFoldTemporary}
  row_length := s6HmrSourceRow_length
  y_length := by simp [s6HmrSourceY]
  out_length := by simp [s6HmrSourceOut]
  anc_length := s6HmrSeamPorts.anc_length
  distinct := by
    simp only [s6HmrSourceRow, s6HmrSourceY, s6HmrSourceOut,
      s6HmrSeamPorts, List.nodup_append, List.nodup_cons,
      List.nodup_reverse]
    all_goals simp [List.mem_range',
      List.nodup_range' (s := 4) (n := 252),
      List.nodup_range' (s := 256) (n := 256),
      List.nodup_range' (s := 512) (n := 256)]
    all_goals repeat' first | constructor | intro
    all_goals try dsimp [Wire] at *
    all_goals omega
  flags_separate := by
    simp [s6HmrSourceRow, s6HmrSourceY, s6HmrSourceOut,
      s6HmrSeamPorts, s6HmrFoldTemporary, List.mem_range']
    repeat' first | constructor | intro
    all_goals omega


/-- Builder allocation before circuit.py seam mm.on; distinct from walk ownership. -/
def s2HmrBeforeSeam : Arena :=
  ⟨arenaWires \ {783, 789, 792, 802, 803, 805, 807, 809, 810, 819, 824, 825, 826, 832, 834, 836, 837, 840, 841, 847, 851, 867, 907, 921, 923, 924, 926, 927, 928, 929, 930, 931, 932, 933, 934}, Finset.sdiff_subset⟩

theorem s2HmrSeam_reserve :
    ∃ B, s2HmrBeforeSeam.reserve
      (s2HmrSeamPorts.flag :: s2HmrSeamPorts.anc).toFinset = some B := by
  rw [Arena.reserve_success]
  decide +kernel

/-- Builder allocation before circuit.py seam mm.on; distinct from walk ownership. -/
def s6HmrBeforeSeam : Arena :=
  ⟨arenaWires \ {782, 784, 790, 792, 794, 796, 797, 800, 802, 807, 814, 818, 821, 823, 832, 841, 848, 850, 853, 863, 864, 867, 868, 869, 880, 888, 891, 916, 922, 928, 929, 930, 931, 933, 934}, Finset.sdiff_subset⟩

theorem s6HmrSeam_reserve :
    ∃ B, s6HmrBeforeSeam.reserve
      (s6HmrSeamPorts.flag :: s6HmrSeamPorts.anc).toFinset = some B := by
  rw [Arena.reserve_success]
  decide +kernel

/-- Source engine.py:3326–3335: unpark folds back using the demolished y word.
This generated block does not assert its lifecycle preconditions or source refinement. -/
def s2HmrSourceUnpark : RecordedProgram := embedRecorded (
  placedRowFold (fusedPlacementMap (fusedFoldPlacement
    s2HmrSourceLayout.row.payload s2HmrSourceLayout.y s2HmrSourceLayout.anc)) true ++
  placedMagnitude (fusedPlacementMap
    (s2HmrSourceLayout.row.sign :: s2HmrSourceLayout.row.payload ++
      s2HmrSourceLayout.anc)) true)


def s2HmrAfterSeam : Arena :=
  (s2HmrBeforeSeam.reserve (s2HmrSeamPorts.flag :: s2HmrSeamPorts.anc).toFinset).get
    (Option.isSome_iff_exists.mpr s2HmrSeam_reserve)

theorem s2HmrSeam_reserve_eq :
    s2HmrBeforeSeam.reserve (s2HmrSeamPorts.flag :: s2HmrSeamPorts.anc).toFinset =
      some s2HmrAfterSeam :=
  Option.eq_some_of_isSome (Option.isSome_iff_exists.mpr s2HmrSeam_reserve)

def s6HmrAfterSeam : Arena :=
  (s6HmrBeforeSeam.reserve (s6HmrSeamPorts.flag :: s6HmrSeamPorts.anc).toFinset).get
    (Option.isSome_iff_exists.mpr s6HmrSeam_reserve)

theorem s6HmrSeam_reserve_eq :
    s6HmrBeforeSeam.reserve (s6HmrSeamPorts.flag :: s6HmrSeamPorts.anc).toFinset =
      some s6HmrAfterSeam :=
  Option.eq_some_of_isSome (Option.isSome_iff_exists.mpr s6HmrSeam_reserve)


private theorem reserve_live_eq (A B : Arena) (qs : Finset Wire)
    (h : A.reserve qs = some B) : B.live = A.live ∪ qs := by
  unfold Arena.reserve at h
  split at h
  next => cases h; rfl
  next => simp at h

/-- Independent transcription of exported after_allocated, not defined by reserve. -/
def s2HmrExportedAfterSeam : Arena :=
  ⟨arenaWires \ {921, 923, 924, 927, 928, 930, 931, 932, 933, 934}, Finset.sdiff_subset⟩

theorem s2HmrAfterSeam_matches_export :
    s2HmrAfterSeam.live = s2HmrExportedAfterSeam.live := by
  rw [reserve_live_eq _ _ _ s2HmrSeam_reserve_eq]
  ext q
  dsimp [Wire] at q
  simp [s2HmrBeforeSeam, s2HmrExportedAfterSeam, s2HmrSeamPorts, arenaWires]
  dsimp [Wire] at *
  omega

/-- Independent transcription of exported after_allocated, not defined by reserve. -/
def s6HmrExportedAfterSeam : Arena :=
  ⟨arenaWires \ {782, 790, 800, 832, 916, 928, 929, 931, 933, 934}, Finset.sdiff_subset⟩

theorem s6HmrAfterSeam_matches_export :
    s6HmrAfterSeam.live = s6HmrExportedAfterSeam.live := by
  rw [reserve_live_eq _ _ _ s6HmrSeam_reserve_eq]
  ext q
  dsimp [Wire] at q
  simp [s6HmrBeforeSeam, s6HmrExportedAfterSeam, s6HmrSeamPorts, arenaWires]
  dsimp [Wire] at *
  omega


private theorem release_live_eq (A B : Arena) (qs : Finset Wire) (state : BasisState)
    (h : A.release qs state = some B) : B.live = A.live \ qs := by
  unfold Arena.release at h
  split at h
  next => cases h; rfl
  next => simp at h

/-- Builder allocation at the actual row_mul boundary, after closer/repack.
This is not HomePool ownership and does not assert any bit is zero. -/
def s2HmrCallArena : Arena :=
  ⟨arenaWires \ {779, 784, 785, 787, 788, 790, 793, 801, 804, 806, 808, 811, 815, 817, 821, 829, 830, 831, 842, 877, 879, 882, 885, 894, 901, 913, 915, 916, 917, 919, 921, 922, 923, 924, 927, 928, 930, 931, 932, 933, 934}, Finset.sdiff_subset⟩

theorem s2HmrFoldTemporary_reserve :
    ∃ B, s2HmrCallArena.reserve {s2HmrFoldTemporary} = some B := by
  rw [Arena.reserve_success]
  decide +kernel

/-- Release returns the original allocation only under an explicit post-execution
zero premise. The source R event supplies no such proof by itself. -/
theorem s2HmrFoldTemporary_return (B : Arena) (state : BasisState)
    (borrow : s2HmrCallArena.reserve {s2HmrFoldTemporary} = some B)
    (zero : state s2HmrFoldTemporary = false) :
    ∃ C, B.release {s2HmrFoldTemporary} state = some C ∧
      C.live = s2HmrCallArena.live := by
  have live := reserve_live_eq _ _ _ borrow
  have disjoint := ((Arena.reserve_success _ _).mp ⟨B, borrow⟩).2
  obtain ⟨C, released⟩ := (Arena.release_success B {s2HmrFoldTemporary} state).mpr
    ⟨by rw [live]; exact Finset.subset_union_right, by simpa using zero⟩
  refine ⟨C, released, ?_⟩
  rw [release_live_eq _ _ _ _ released, live]
  exact Finset.union_sdiff_cancel_right disjoint

/-- Builder allocation at the actual row_mul boundary, after closer/repack.
This is not HomePool ownership and does not assert any bit is zero. -/
def s6HmrCallArena : Arena :=
  ⟨arenaWires \ {778, 782, 786, 789, 790, 791, 793, 798, 800, 810, 816, 817, 820, 825, 828, 830, 832, 833, 842, 854, 856, 857, 859, 860, 865, 873, 875, 876, 882, 898, 903, 914, 915, 916, 920, 927, 928, 929, 931, 933, 934}, Finset.sdiff_subset⟩

theorem s6HmrFoldTemporary_reserve :
    ∃ B, s6HmrCallArena.reserve {s6HmrFoldTemporary} = some B := by
  rw [Arena.reserve_success]
  decide +kernel

/-- Release returns the original allocation only under an explicit post-execution
zero premise. The source R event supplies no such proof by itself. -/
theorem s6HmrFoldTemporary_return (B : Arena) (state : BasisState)
    (borrow : s6HmrCallArena.reserve {s6HmrFoldTemporary} = some B)
    (zero : state s6HmrFoldTemporary = false) :
    ∃ C, B.release {s6HmrFoldTemporary} state = some C ∧
      C.live = s6HmrCallArena.live := by
  have live := reserve_live_eq _ _ _ borrow
  have disjoint := ((Arena.reserve_success _ _).mp ⟨B, borrow⟩).2
  obtain ⟨C, released⟩ := (Arena.release_success B {s6HmrFoldTemporary} state).mpr
    ⟨by rw [live]; exact Finset.subset_union_right, by simpa using zero⟩
  refine ⟨C, released, ?_⟩
  rw [release_live_eq _ _ _ _ released, live]
  exact Finset.union_sdiff_cancel_right disjoint

end ECDSAAdd.Arithmetic.Paper935
