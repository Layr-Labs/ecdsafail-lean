import ECDSAAdd.Arithmetic.Paper935.RowResize

namespace ECDSAAdd.Arithmetic.Paper935

/-- Two unsigned payload views grow from opposite ends of one host. Sign
wires are separate and are not silently included in this host's capacity. -/
structure PackedHost where
  base : Nat
  capacity : Nat
  leftWidth : Nat
  rightWidth : Nat
  bounded : base+capacity≤935
  fits : leftWidth+rightWidth≤capacity

def PackedHost.left (H : PackedHost) : List Wire := List.range' H.base H.leftWidth

def PackedHost.right (H : PackedHost) : List Wire :=
  (List.range' (H.base+H.capacity-H.rightWidth) H.rightWidth).reverse

def PackedHost.host (H : PackedHost) : Finset Wire := Finset.Ico H.base (H.base+H.capacity)
def PackedHost.live (H : PackedHost) : Finset Wire := (H.left++H.right).toFinset
def PackedHost.gap (H : PackedHost) : Finset Wire :=
  Finset.Ico (H.base+H.leftWidth) (H.base+H.capacity-H.rightWidth)

/-- Capacity and arena bounds are checked, not supplied as constructor
proofs by clients of the layout generator. -/
def packedHost (base capacity leftWidth rightWidth : Nat) : Option PackedHost :=
  if h : base+capacity≤935 ∧ leftWidth+rightWidth≤capacity then
    some ⟨base,capacity,leftWidth,rightWidth,h.1,h.2⟩
  else none

theorem packedHost_success (base capacity leftWidth rightWidth : Nat) :
    (∃ H,packedHost base capacity leftWidth rightWidth=some H) ↔
      base+capacity≤935 ∧ leftWidth+rightWidth≤capacity := by
  unfold packedHost
  split <;> simp_all

theorem PackedHost.left_mem (H : PackedHost) (q : Wire) :
    q∈H.left ↔ H.base≤q ∧ q<H.base+H.leftWidth := by
  simp [left,List.mem_range'_1]

theorem PackedHost.right_mem (H : PackedHost) (q : Wire) :
    q∈H.right ↔ H.base+H.capacity-H.rightWidth≤q ∧ q<H.base+H.capacity := by
  have hf := H.fits
  simp only [right,List.mem_reverse,List.mem_range'_1]
  simp only [Wire] at *
  omega

theorem PackedHost.widths (H : PackedHost) :
    H.left.length=H.leftWidth ∧ H.right.length=H.rightWidth := by
  simp [left,right]

theorem PackedHost.distinct (H : PackedHost) : (H.left++H.right).Nodup := by
  rw [List.nodup_append]
  refine ⟨?_,?_,?_⟩
  · simp [left,List.nodup_range']
  · simp [right,List.nodup_range']
  · intro q hl r hr he
    subst r
    have h1 := (H.left_mem q).mp hl
    have h2 := (H.right_mem q).mp hr
    have hf := H.fits
    simp only [Wire] at *
    omega

theorem PackedHost.live_in_host (H : PackedHost) : H.live⊆H.host := by
  intro q hq
  simp only [live,List.mem_toFinset,List.mem_append] at hq
  simp only [host,Finset.mem_Ico]
  have hf := H.fits
  rcases hq with hl | hr
  · have h := (H.left_mem q).mp hl
    simp only [Wire] at *
    omega
  · have h := (H.right_mem q).mp hr
    simp only [Wire] at *
    omega

theorem PackedHost.host_in_arena (H : PackedHost) : H.host⊆arenaWires := by
  intro q hq
  have hb := H.bounded
  simp only [host,Finset.mem_Ico] at hq
  simp only [arenaWires,Finset.mem_range]
  simp only [Wire] at *
  omega

theorem PackedHost.gap_exact (H : PackedHost) : H.gap=H.host\H.live := by
  ext q
  simp only [gap,host,live,Finset.mem_Ico,Finset.mem_sdiff,List.mem_toFinset,
    List.mem_append,H.left_mem,H.right_mem]
  have hf := H.fits
  simp only [Wire] at *
  omega

theorem PackedHost.live_count (H : PackedHost) : H.live.card=H.leftWidth+H.rightWidth := by
  rw [live,List.toFinset_card_of_nodup H.distinct,List.length_append,H.widths.1,H.widths.2]

theorem PackedHost.gap_count (H : PackedHost) : H.gap.card=H.capacity-(H.leftWidth+H.rightWidth) := by
  simp only [gap,Nat.card_Ico]
  have hf := H.fits
  omega

/-- If the payloads do not fill the host, the next left high bit is exactly
at the free-gap boundary; it aliases neither payload. -/
theorem PackedHost.left_growth_slot (H : PackedHost) (hf : H.leftWidth+H.rightWidth<H.capacity) :
    H.base+H.leftWidth∈H.gap ∧ H.base+H.leftWidth∉H.live ∧
      H.base+H.leftWidth∈arenaWires := by
  have hg : H.base+H.leftWidth∈H.gap := by
    simp only [gap,Finset.mem_Ico]
    omega
  have hm := hg
  rw [H.gap_exact] at hm
  exact ⟨hg,(Finset.mem_sdiff.mp hm).2,H.host_in_arena (Finset.mem_sdiff.mp hm).1⟩

theorem PackedHost.right_growth_slot (H : PackedHost) (hf : H.leftWidth+H.rightWidth<H.capacity) :
    H.base+H.capacity-H.rightWidth-1∈H.gap ∧
      H.base+H.capacity-H.rightWidth-1∉H.live ∧
      H.base+H.capacity-H.rightWidth-1∈arenaWires := by
  have hg : H.base+H.capacity-H.rightWidth-1∈H.gap := by
    simp only [gap,Finset.mem_Ico]
    omega
  have hm := hg
  rw [H.gap_exact] at hm
  exact ⟨hg,(Finset.mem_sdiff.mp hm).2,H.host_in_arena (Finset.mem_sdiff.mp hm).1⟩

/-- The two paper host bands have independent checked payload capacities.
This constructor does not claim that any divsteps trajectory fits them. -/
def pairedHosts (f gv g fv : Nat) : Option (PackedHost × PackedHost) := do
  let a ← packedHost 0 256 f gv
  let b ← packedHost 256 256 g fv
  pure (a,b)

theorem pairedHosts_success (f gv g fv : Nat) :
    (∃ a b,pairedHosts f gv g fv=some (a,b)) ↔ f+gv≤256 ∧ g+fv≤256 := by
  simp [pairedHosts,packedHost]
  split <;> split <;> simp_all

/-- Two ordered host bands cannot alias, regardless of their payload widths. -/
theorem PackedHost.separated (H K : PackedHost) (h : H.base+H.capacity≤K.base) :
    Disjoint H.live K.live := by
  apply Finset.disjoint_left.mpr
  intro q hq hk
  have ha := H.live_in_host hq
  have hb := K.live_in_host hk
  simp only [host,Finset.mem_Ico,Wire] at ha hb
  omega

/-- Any free gap site can be used by the physical sign-extension gate. The
surrounding arena may also own sign, counter and coordinate registers. -/
theorem PackedHost.grow_payload (H : PackedHost) (A : Arena) (lo : List Wire)
    (sign top : Wire) (s : State) (m : List Bool)
    (hl : lo.toFinset⊆H.live) (ha : H.live⊆A.live) (hs : sign∈A.live)
    (hg : top∈H.gap) (hfree : Disjoint A.live H.gap) (hr : A.Ready s.basis) :
    ∃ B,A.reserve {top}=some B ∧
      B.Ready (run (resizeBit sign top) m s).basis ∧
      signedRegValue ((lo++[top])++[sign]) (run (resizeBit sign top) m s).basis=
        signedRegValue (lo++[sign]) s.basis ∧
      wires (resizeBit sign top)⊆arenaWires := by
  have hgap := hg
  rw [H.gap_exact] at hgap
  have ht := H.host_in_arena (Finset.mem_sdiff.mp hgap).1
  have hn : top∉A.live := fun h => Finset.disjoint_left.mp hfree h hg
  obtain ⟨B,hB⟩ := (A.reserve_success {top}).mpr
    ⟨by simpa using ht,by simpa using hn⟩
  have hv := rowGrow_reserved A B lo sign top hs (hl.trans ha) s m hr hB
  exact ⟨B,hB,hv.1,hv.2,resize_in_arena sign top (A.bounded hs) ht⟩

end ECDSAAdd.Arithmetic.Paper935
