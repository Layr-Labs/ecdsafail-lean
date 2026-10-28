import ECDSAAdd.Arithmetic.Paper935.PackedHost

namespace ECDSAAdd.Arithmetic.Paper935

/-- Increase one payload width only when a physical gap site exists. -/
def PackedHost.growLeft (H : PackedHost) (h : H.leftWidth+H.rightWidth<H.capacity) : PackedHost :=
  ⟨H.base,H.capacity,H.leftWidth+1,H.rightWidth,H.bounded,by omega⟩

def PackedHost.growRight (H : PackedHost) (h : H.leftWidth+H.rightWidth<H.capacity) : PackedHost :=
  ⟨H.base,H.capacity,H.leftWidth,H.rightWidth+1,H.bounded,by omega⟩

theorem PackedHost.growLeft_views (H : PackedHost) (h : H.leftWidth+H.rightWidth<H.capacity) :
    (H.growLeft h).left=H.left++[H.base+H.leftWidth] ∧
      (H.growLeft h).right=H.right := by
  constructor
  · simpa [growLeft,left] using
      (List.range'_append_1 (s := H.base) (m := H.leftWidth) (n := 1)).symm
  · rfl

theorem PackedHost.growRight_views (H : PackedHost) (h : H.leftWidth+H.rightWidth<H.capacity) :
    (H.growRight h).right=H.right++[H.base+H.capacity-H.rightWidth-1] ∧
      (H.growRight h).left=H.left := by
  constructor
  · have he : H.base+H.capacity-H.rightWidth-1+1=H.base+H.capacity-H.rightWidth := by omega
    have ht : H.base+H.capacity-(H.rightWidth+1)=H.base+H.capacity-H.rightWidth-1 := by omega
    simp only [growRight,right,List.range'_succ,List.reverse_cons,ht,he]
  · rfl

theorem PackedHost.growLeft_live (H : PackedHost) (h : H.leftWidth+H.rightWidth<H.capacity) :
    (H.growLeft h).live=insert (H.base+H.leftWidth) H.live := by
  ext q
  simp only [live,List.mem_toFinset,List.mem_append,Finset.mem_insert,
    (H.growLeft_views h).1,(H.growLeft_views h).2,List.mem_singleton]
  tauto

theorem PackedHost.growRight_live (H : PackedHost) (h : H.leftWidth+H.rightWidth<H.capacity) :
    (H.growRight h).live=insert (H.base+H.capacity-H.rightWidth-1) H.live := by
  ext q
  simp only [live,List.mem_toFinset,List.mem_append,Finset.mem_insert,
    (H.growRight_views h).1,(H.growRight_views h).2,List.mem_singleton]
  tauto

private theorem reserved_live (A B : Arena) (top : Wire) (h : A.reserve {top}=some B) :
    B.live=insert top A.live := by
  unfold Arena.reserve at h
  split at h
  · cases h; simp
  · simp at h

/-- Left growth changes the actual payload view to the checked larger layout,
while retaining ownership of the opposite row and all surrounding registers. -/
theorem PackedHost.growLeft_run (H : PackedHost) (A : Arena) (sign : Wire)
    (h : H.leftWidth+H.rightWidth<H.capacity) (s : State) (m : List Bool)
    (ha : H.live⊆A.live) (hs : sign∈A.live) (hfree : Disjoint A.live H.gap)
    (hr : A.Ready s.basis) :
    ∃ B,A.reserve {H.base+H.leftWidth}=some B ∧
      (H.growLeft h).live⊆B.live ∧
      B.Ready (run (resizeBit sign (H.base+H.leftWidth)) m s).basis ∧
      signedRegValue ((H.growLeft h).left++[sign])
        (run (resizeBit sign (H.base+H.leftWidth)) m s).basis=
        signedRegValue (H.left++[sign]) s.basis := by
  obtain ⟨B,hB,hready,hvalue,_⟩ := H.grow_payload A H.left sign (H.base+H.leftWidth) s m
    (by intro q hq; simp only [live,List.toFinset_append]; exact Finset.mem_union_left _ hq)
    ha hs (H.left_growth_slot h).1 hfree hr
  refine ⟨B,hB,?_,hready,?_⟩
  · rw [H.growLeft_live h,reserved_live A B _ hB]
    exact Finset.insert_subset_insert _ ha
  · simpa only [(H.growLeft_views h).1] using hvalue

theorem PackedHost.growRight_run (H : PackedHost) (A : Arena) (sign : Wire)
    (h : H.leftWidth+H.rightWidth<H.capacity) (s : State) (m : List Bool)
    (ha : H.live⊆A.live) (hs : sign∈A.live) (hfree : Disjoint A.live H.gap)
    (hr : A.Ready s.basis) :
    ∃ B,A.reserve {H.base+H.capacity-H.rightWidth-1}=some B ∧
      (H.growRight h).live⊆B.live ∧
      B.Ready (run (resizeBit sign (H.base+H.capacity-H.rightWidth-1)) m s).basis ∧
      signedRegValue ((H.growRight h).right++[sign])
        (run (resizeBit sign (H.base+H.capacity-H.rightWidth-1)) m s).basis=
        signedRegValue (H.right++[sign]) s.basis := by
  obtain ⟨B,hB,hready,hvalue,_⟩ := H.grow_payload A H.right sign
    (H.base+H.capacity-H.rightWidth-1) s m
    (by intro q hq; simp only [live,List.toFinset_append]; exact Finset.mem_union_right _ hq)
    ha hs (H.right_growth_slot h).1 hfree hr
  refine ⟨B,hB,?_,hready,?_⟩
  · rw [H.growRight_live h,reserved_live A B _ hB]
    exact Finset.insert_subset_insert _ ha
  · simpa only [(H.growRight_views h).1] using hvalue

/-- Reversing the resize gate restores the entire physical state, including
arbitrary surrounding registers and phase. No measurement tape is consumed. -/
theorem resizeBit_roundtrip (sign top : Wire) (hne : sign≠top) (s : State) (m n : List Bool) :
    run (resizeBit sign top) n (run (resizeBit sign top) m s)=s := by
  apply congrArg₂ State.mk
  · rfl
  · funext q
    by_cases hq : q=top
    · subst q
      cases hs : s.basis sign <;> cases ht : s.basis top <;>
        simp [resizeBit,run,writeBit,hne,hs,ht]
    · simp [resizeBit,run,writeBit,hq]

private theorem release_reserved_clean (A B : Arena) (top : Wire) (s : BasisState)
    (hB : A.reserve {top}=some B) (hz : s top=false) : B.release {top} s=some A := by
  have hv := (A.reserve_success {top}).mp ⟨B,hB⟩
  have hn : top∉A.live := fun h => Finset.disjoint_left.mp hv.2 h (by simp)
  have hl := reserved_live A B top hB
  have hc : {top}⊆B.live ∧ ∀ q∈({top}:Finset Wire),s q=false := by simp [hl,hz]
  unfold Arena.release
  rw [if_pos hc]
  apply congrArg some
  have heq : B.live\{top}=A.live := by
    rw [hl]
    ext q
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · intro h; rcases h.1 with he | he
      · exact False.elim (h.2 he)
      · exact he
    · intro h
      exact ⟨Or.inr h,fun he => hn (he ▸ h)⟩
  cases A with
  | mk alive abound =>
    change Arena.mk _ _ = Arena.mk alive abound
    cases heq
    rfl

/-- The inverse physical gate restores both the entire input state and the
exact allocator ownership that preceded growth. -/
theorem reserve_resize_release (A B : Arena) (sign top : Wire) (s : State) (m : List Bool)
    (hs : sign∈A.live) (hr : A.Ready s.basis) (hB : A.reserve {top}=some B) :
    let t := run (resizeBit sign top) m (run (resizeBit sign top) [] s)
    B.release {top} t.basis=some A ∧ t=s := by
  have hv := (A.reserve_success {top}).mp ⟨B,hB⟩
  have hn : top∉A.live := fun h => Finset.disjoint_left.mp hv.2 h (by simp)
  have he : sign≠top := fun h => hn (h ▸ hs)
  have hz : s.basis top=false := hr top (by simpa using hv.1) hn
  dsimp only
  rw [resizeBit_roundtrip sign top he s [] m]
  exact ⟨release_reserved_clean A B top s.basis hB hz,rfl⟩

/-- Shrink arbitrary wide-row states whose integer fits the narrower signed
window, not only states just produced by growth. The width bound derives
redundant sign equality and the CX clears the returned physical bit. -/
theorem shrink_reserved_run (A B : Arena) (lo : List Wire) (sign top : Wire)
    (s : State) (m : List Bool) (hB : A.reserve {top}=some B)
    (hl : lo.toFinset⊆A.live) (hs : sign∈A.live) (hr : B.Ready s.basis)
    (hlo : -((2^lo.length:Nat):Int)≤signedRegValue ((lo++[top])++[sign]) s.basis)
    (hhi : signedRegValue ((lo++[top])++[sign]) s.basis<((2^lo.length:Nat):Int)) :
    let t := run (resizeBit sign top) m s
    B.release {top} t.basis=some A ∧ A.Ready t.basis ∧
      signedRegValue (lo++[sign]) t.basis=signedRegValue ((lo++[top])++[sign]) s.basis := by
  have hv := (A.reserve_success {top}).mp ⟨B,hB⟩
  have hn : top∉A.live := fun h => Finset.disjoint_left.mp hv.2 h (by simp)
  have ht : top∉lo := fun h => hn (hl (List.mem_toFinset.mpr h))
  have he : sign≠top := fun h => hn (h ▸ hs)
  have hout := rowShrink_run lo sign top ht he s m (rowShrink_bit_of_fits lo sign top s.basis hlo hhi)
  refine ⟨release_reserved_clean A B top _ hB hout.2.2.1,?_,hout.2.2.2⟩
  intro q hq hnot
  by_cases hqt : q=top
  · subst q; exact hout.2.2.1
  · rw [hout.2.1 q hqt]
    apply hr q hq
    rw [reserved_live A B top hB]
    simpa [hqt] using hnot

end ECDSAAdd.Arithmetic.Paper935
