import ECDSAAdd.Arithmetic.FusedSharedRetainedDivision
import ECDSAAdd.Arithmetic.CompactGuardSupport

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic



attribute [local irreducible] wireBlock swapRegisters dblInPlace copyRegister
attribute [local irreducible] fusedSharedRetainedCell fusedSharedRetainedReplay

private theorem retained_block_subset_shared (w : Nat → Wire) (s n : Nat)
    (hb : s+n≤2314) : wireBlock w s n ⊆ skywalkSharedWires w := by
  intro q hq
  rw [wireBlock] at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  rw [skywalkSharedWires,wireBlock]
  apply List.mem_map.mpr
  have hi' := List.mem_range'_1.mp hi
  exact ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem retained_field_subset_shared (w : Nat → Wire) :
    (skywalkSharedField w).wires⊆skywalkSharedWires w := by
  intro q hq
  unfold ModInPlaceLayout.wires at hq
  rw [skywalkShared_field_z] at hq
  change q∈wireBlock w 770 257++wireBlock w 2056 257++
    (wireBlock w 1540 257++wireBlock w 1798 256++[w 1797]++
      wireBlock w 512 257++[w 2313]) at hq
  simp only [List.mem_append,List.mem_singleton,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq|hq|hq
  · exact retained_block_subset_shared w 770 257 (by omega) hq
  · exact retained_block_subset_shared w 2056 257 (by omega) hq
  · exact retained_block_subset_shared w 1540 257 (by omega) hq
  · exact retained_block_subset_shared w 1798 256 (by omega) hq
  · subst q
    exact retained_block_subset_shared w 1797 1 (by omega) (by simp [wireBlock])
  · exact retained_block_subset_shared w 512 257 (by omega) hq
  · subst q
    exact retained_block_subset_shared w 2313 1 (by omega) (by simp [wireBlock])

theorem retained_tape_subset_shared (w : Nat → Wire) :
    ∀ r∈skywalkSharedTape w,r.1∈skywalkSharedWires w ∧
      r.2∈skywalkSharedWires w := by
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  have hib : i<512 := List.mem_range.mp hi
  constructor
  · exact retained_block_subset_shared w i 1 (by omega) (by simp [wireBlock])
  · exact retained_block_subset_shared w (1028+i) 1 (by omega) (by simp [wireBlock])

theorem fusedSharedRetainedKernel_support (w : Nat → Wire) (g : Wire)
    (hg : g∈skywalkSharedWires w) :
    wires (fusedSharedPorts w g).compactForwardProgram⊆(skywalkSharedWires w).toFinset := by
  have hs := (fusedSharedPorts w g).compact_forward_support
    (fusedSharedPorts_widths w g) (fusedSharedPorts_early w g)
  exact hs.trans (by
    intro q hq
    rw [fusedSharedPorts_wires] at hq
    apply List.mem_toFinset.mpr
    rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with rfl|hq
    · exact hg
    · exact fusedSharedSites_subset w hq)

theorem fusedSharedRetainedSignedHalf_support (w : Nat → Wire) (g : Wire)
    (hg : g∈skywalkSharedWires w) :
    wires (fusedSharedRetainedSignedHalf w g)⊆(skywalkSharedWires w).toFinset := by
  have hk := fusedSharedRetainedKernel_support w g hg
  have hx : wires [.X g]⊆(skywalkSharedWires w).toFinset := by
    intro q hq
    have heq : q=g := by simpa [wires,Instr.wires] using hq
    subst q
    exact List.mem_toFinset.mpr hg
  simp only [fusedSharedRetainedSignedHalf,fusedFieldSignedHalf,wires_append,
    Finset.union_subset_iff]
  aesop

theorem fusedSharedRetainedCell_support (w : Nat → Wire) (g swap : Wire)
    (hg : g∈skywalkSharedWires w) (hswap : swap∈skywalkSharedWires w) :
    wires (fusedSharedRetainedCell w g swap)⊆(skywalkSharedWires w).toFinset := by
  have hk := fusedSharedRetainedSignedHalf_support w g hg
  have hw := skywalkShared_field_widths w
  have hlen : ((skywalkSharedField w).z.take (skywalkSharedField w).low.length).length=
      ((skywalkSharedField w).a.take (skywalkSharedField w).low.length).length := by
    simp [List.length_take,ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hs := swapRegisters_wires swap
    ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
    ((skywalkSharedField w).a.take (skywalkSharedField w).low.length) hlen
  have hs' : wires (swapRegisters swap
      ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
      ((skywalkSharedField w).a.take (skywalkSharedField w).low.length))⊆
      (skywalkSharedWires w).toFinset := by
    intro q hq
    apply List.mem_toFinset.mpr
    have hq' := hs hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq'
    rcases hq' with rfl|hz|ha
    · exact hswap
    · exact retained_field_subset_shared w
        (by simp [ModInPlaceLayout.wires,List.mem_of_mem_take hz])
    · exact retained_field_subset_shared w
        (by simp [ModInPlaceLayout.wires,List.mem_of_mem_take ha])
  simp only [fusedSharedRetainedCell,wires_append,Finset.union_subset_iff]
  exact ⟨hk,hs'⟩

theorem fusedSharedRetainedReplay_support (w : Nat → Wire)
    (rs : List (Wire×Wire))
    (ht : ∀ r∈rs,r.1∈skywalkSharedWires w ∧ r.2∈skywalkSharedWires w) :
    wires (fusedSharedRetainedReplay w rs)⊆(skywalkSharedWires w).toFinset := by
  induction rs with
  | nil => simp [fusedSharedRetainedReplay,wires]
  | cons r rs ih =>
    have hr := ht r (by simp)
    have ht' : ∀ q∈rs,q.1∈skywalkSharedWires w ∧ q.2∈skywalkSharedWires w :=
      fun q hq => ht q (by simp [hq])
    have hc := fusedSharedRetainedCell_support w r.1 r.2 hr.1 hr.2
    have hi := ih ht'
    simp only [fusedSharedRetainedReplay,wires_append,Finset.union_subset_iff]
    exact ⟨hc,hi⟩

theorem skywalkFieldDivisionRetained_support (w : Nat → Wire) :
    wires (skywalkFieldDivisionRetained w)⊆(skywalkSharedWires w).toFinset := by
  have hw := skywalkShared_field_widths w
  have hu := modUnary_wires (skywalkSharedField w).unary 256 p
    ((skywalkSharedField w).unary_widths 256 hw) (by omega)
  have hd : wires (dblInPlace (skywalkSharedField w).unary p)⊆
      (skywalkSharedWires w).toFinset := by
    rw [hu.1]
    intro q hq
    apply List.mem_toFinset.mpr
    apply retained_field_subset_shared w
    simp only [List.mem_toFinset,List.mem_append,ModInPlaceLayout.wires,
      ModInPlaceLayout.work,ModInPlaceLayout.unary,ModUnaryLayout.z,
      ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,
      ModInPlaceLayout.z] at hq ⊢
    tauto
  have hr := fusedSharedRetainedReplay_support w (skywalkSharedTape w)
    (retained_tape_subset_shared w)
  have hlen : (skywalkSharedField w).z.length=(skywalkSharedField w).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hc0 := copyRegister_wires none (skywalkSharedField w).z
    (skywalkSharedField w).a hlen
  have hc : wires (copyRegister none (skywalkSharedField w).z
      (skywalkSharedField w).a)⊆(skywalkSharedWires w).toFinset := by
    rw [hc0]
    split
    · exact Finset.empty_subset _
    · intro q hq
      apply List.mem_toFinset.mpr
      apply retained_field_subset_shared w
      simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
      rcases hq with hz|ha
      · simp [ModInPlaceLayout.wires,hz]
      · simp [ModInPlaceLayout.wires,ha]
  simp only [skywalkFieldDivisionRetained,wires_append,Finset.union_subset_iff]
  aesop

end ECDSAAdd.Arithmetic
