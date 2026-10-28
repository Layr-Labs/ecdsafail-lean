import ECDSAAdd.Framework.RecordedPermutation
import ECDSAAdd.Arithmetic.Paper935.Arena

namespace ECDSAAdd.Arithmetic.Paper935

/-- A finite physical arena permutation, represented on all wires for state
pullback. No image of the infinite wire type is required to be finite. -/
structure ArenaPermutation where
  equiv : Equiv.Perm Wire
  preserves : ∀ q,equiv q∈arenaWires ↔ q∈arenaWires

noncomputable def ArenaPermutation.ofFinite (f : Wire → Wire)
    (inj : Set.InjOn f arenaWires) (image : arenaWires.image f=arenaWires) : ArenaPermutation :=
  ⟨finiteWirePermutation arenaWires f inj image,finiteWirePermutation_preserves arenaWires f inj image⟩

def Arena.renamed (A : Arena) (e : ArenaPermutation) : Arena :=
  ⟨A.live.image e.equiv,by
    intro q hq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    exact (e.preserves a).mpr (A.bounded ha)⟩

theorem Arena.renamed_card (A : Arena) (e : ArenaPermutation) :
    (A.renamed e).live.card=A.live.card := Finset.card_image_of_injective _ e.equiv.injective

theorem Arena.renamed_ready (A : Arena) (e : ArenaPermutation) (s : BasisState) :
    (A.renamed e).Ready s ↔ A.Ready (fun q => s (e.equiv q)) := by
  constructor
  · intro ready q hq hn
    apply ready (e.equiv q) ((e.preserves q).mpr hq)
    simpa only [Arena.renamed,Finset.mem_image,e.equiv.injective.eq_iff,exists_eq_right] using hn
  · intro ready q hq hn
    obtain ⟨a,rfl⟩ := e.equiv.surjective q
    apply ready a ((e.preserves a).mp hq)
    intro ha
    exact hn (Finset.mem_image_of_mem _ ha)

theorem ArenaPermutation.disjoint_image (e : ArenaPermutation) (A B : Finset Wire) :
    Disjoint (A.image e.equiv) (B.image e.equiv) ↔ Disjoint A B := by
  exact Finset.disjoint_image e.equiv.injective

theorem ArenaPermutation.image_subset (e : ArenaPermutation) (A B : Finset Wire)
    (sub : A⊆B) : A.image e.equiv⊆B.image e.equiv := Finset.image_subset_image sub

theorem ArenaPermutation.image_arena (e : ArenaPermutation) : arenaWires.image e.equiv=arenaWires := by
  ext q
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    exact (e.preserves a).mpr ha
  · intro h
    obtain ⟨a,rfl⟩ := e.equiv.surjective q
    exact Finset.mem_image_of_mem _ ((e.preserves a).mp h)

theorem Arena.renamed_reserve (A B : Arena) (qs : Finset Wire) (e : ArenaPermutation)
    (h : A.reserve qs=some B) : (A.renamed e).reserve (qs.image e.equiv)=some (B.renamed e) := by
  unfold Arena.reserve at h
  split at h
  next valid =>
    cases h
    have bounded : qs.image e.equiv⊆arenaWires := by
      rw [←e.image_arena]
      exact Finset.image_subset_image valid.1
    have apart := (e.disjoint_image A.live qs).mpr valid.2
    simp only [Arena.reserve,Arena.renamed,Finset.image_union]
    rw [dif_pos (And.intro bounded apart)]
  next invalid => simp at h

theorem Arena.renamed_release (A B : Arena) (qs : Finset Wire) (e : ArenaPermutation) (s : BasisState)
    (h : A.release qs (fun q => s (e.equiv q))=some B) :
    (A.renamed e).release (qs.image e.equiv) s=some (B.renamed e) := by
  unfold Arena.release at h
  split at h
  next valid =>
    cases h
    have bounded : qs.image e.equiv⊆A.live.image e.equiv := Finset.image_subset_image valid.1
    have clean : ∀q∈qs.image e.equiv,s q=false := by
      intro q hq
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
      exact valid.2 a ha
    simp only [Arena.release,Arena.renamed]
    rw [if_pos (And.intro bounded clean)]
    congr 2
    exact (Finset.image_sdiff A.live qs e.equiv.injective).symm
  next invalid => simp at h

end ECDSAAdd.Arithmetic.Paper935
