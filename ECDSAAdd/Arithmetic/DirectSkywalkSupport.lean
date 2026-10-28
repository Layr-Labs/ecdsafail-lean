import ECDSAAdd.Arithmetic.DirectSkywalkKernelSupport

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout DirectSkywalk
attribute [local irreducible] wireBlock directSkywalkArithmetic

/-- Physical support of the actual repaired caller-X circuit. The three
scalar flags use sites 1802--1804; both correction branches are included. -/
theorem pointDirectSkywalkArithmetic_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) :
    wires (pointDirectSkywalkArithmetic L multiply)⊆
      (L.core.generic::L.point.x++L.point.y++wireBlock L.core.poolWire 0 1805).toFinset := by
  let W := (L.core.generic::L.point.x++L.point.y++wireBlock L.core.poolWire 0 1805).toFinset
  have pool (i : Nat) (hi : i<1805) : L.core.poolWire i∈W := by
    simp only [W,List.mem_toFinset,List.mem_append,List.mem_cons,or_assoc]
    exact Or.inr (Or.inr (Or.inr (arith_mem L.core.poolWire 0 1805 i (by omega) hi)))
  have xmem (q : Wire) (hq : q∈L.point.x) : q∈W := by
    simp only [W,List.mem_toFinset,List.mem_append,List.mem_cons,or_assoc]
    exact Or.inr (Or.inl hq)
  have ymem (q : Wire) (hq : q∈L.point.y) : q∈W := by
    simp only [W,List.mem_toFinset,List.mem_append,List.mem_cons,or_assoc]
    exact Or.inr (Or.inr (Or.inl hq))
  have shared : (skywalkSharedWires L.skywalkDirectMap).toFinset⊆W := by
    intro q hq
    have hm := List.mem_toFinset.mp hq
    rcases (skywalkPointWire_mem L.core.poolWire L.point.x L.point.y
      hw.inputX hw.inputY q).mp hm with hp|hx|hy
    · rw [wireBlock] at hp
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
      simp only [List.mem_range'_1] at hj
      exact pool j (by omega)
    · exact xmem q hx
    · exact ymem q hy
  have hb : L.core.generic∈W := by
    simp only [W,List.mem_toFinset,List.mem_append,List.mem_cons,or_assoc]
    exact Or.inl True.intro
  have hg : L.skywalkDirectSelectorG∈W := pool 1802 (by omega)
  have hs : L.skywalkDirectSelectorS∈W := pool 1803 (by omega)
  have hz : L.skywalkDirectZero∈W := pool 1804 (by omega)
  have hi : directSkywalkCin L∈W := pool 1801 (by omega)
  have kernel := DirectSupport.kernel (!multiply) L.skywalkDirectMap
    (L.skywalkDirectMap_nodup hw hn) L.core.generic L.skywalkDirectSelectorG L.skywalkDirectSelectorS
    W shared hb hg hs
  have own : (L.skywalkDirectZero::directSkywalkCin L::(L.point.x++directSkywalkCarry L)).toFinset⊆W := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|hx|hc
    · exact hz
    · exact hi
    · exact xmem q hx
    · rw [directSkywalkCarry,wireBlock] at hc
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_range'_1] at hj
      exact pool j (by omega)
  have repair := (directZeroDivisor_wires L.point.x (directSkywalkCarry L)
    (directSkywalkCin L) L.skywalkDirectZero).trans own
  rw [wires_append] at repair
  have enter : wires (directZeroDivisorEnter L.point.x (directSkywalkCarry L)
      (directSkywalkCin L) L.skywalkDirectZero)⊆W :=
    fun _ h => repair (Finset.mem_union_left _ h)
  have leave : wires (directZeroDivisorLeave L.point.x (directSkywalkCarry L)
      (directSkywalkCin L) L.skywalkDirectZero)⊆W :=
    fun _ h => repair (Finset.mem_union_right _ h)
  simp only [pointDirectSkywalkArithmetic,directZeroControlled,wires_append,Finset.union_subset_iff]
  exact ⟨enter,kernel,leave⟩

/-- The stage allocation also includes resident point/control flags. It is
a support certificate derived from instructions, not from the semantic frame. -/
theorem pointDirectSkywalkArithmetic_declared_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) :
    wires (pointDirectSkywalkArithmetic L multiply)⊆L.skywalkDirectDeclaredSites.toFinset := by
  apply (pointDirectSkywalkArithmetic_support L hw hn multiply).trans
  have hp : wireBlock L.core.poolWire 0 1805=L.dialogPool.take 1805 := by
    rw [L.core.pool_prefix hw 1805 (by omega)]
    simp [dialogPool,List.take_take]
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl|hx|hy|hpool
  · simp [skywalkDirectDeclaredSites,inPlaceFlags]
  · simp [skywalkDirectDeclaredSites,PointAddLayout.pointWires,hx]
  · simp [skywalkDirectDeclaredSites,PointAddLayout.pointWires,hy]
  · rw [hp] at hpool
    simp [skywalkDirectDeclaredSites,hpool]

/-- A certified allocation of 2,326 distinct physical sites covers the
emitted circuit and resident caller registers. This is a peak-live ceiling,
not a claim of the exact or minimum live peak, or the final 1,297-qubit goal. -/
theorem pointDirectSkywalkArithmetic_resource_certificate (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (multiply : Bool) :
    wires (pointDirectSkywalkArithmetic L multiply)⊆L.skywalkDirectDeclaredSites.toFinset ∧
    L.skywalkDirectDeclaredSites.Nodup ∧ L.skywalkDirectDeclaredSites.length=2326 ∧
    qubitCount (pointDirectSkywalkArithmetic L multiply)≤2326 := by
  have support := pointDirectSkywalkArithmetic_declared_support L hw hn multiply
  have nd := L.skywalkDirectDeclaredSites_nodup hn
  have len := L.skywalkDirectDeclaredSites_length hw
  refine ⟨support,nd,len,?_⟩
  unfold qubitCount
  calc
    _ ≤ L.skywalkDirectDeclaredSites.toFinset.card := Finset.card_le_card support
    _ = 2326 := by rw [List.toFinset_card_of_nodup nd,len]

end ECDSAAdd.Arithmetic
