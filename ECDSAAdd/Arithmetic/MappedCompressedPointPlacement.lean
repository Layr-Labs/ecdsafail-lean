import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites
import ECDSAAdd.Arithmetic.SkywalkDirectPointLayout
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open ControlledPointLayout

def pointMeta (L : ControlledPointLayout) : List Wire :=
  [L.core.generic,L.point.finite,L.control,L.infinitySelect,L.doubleSelect,L.genericSelect,
    L.core.equalX,L.core.equalNegY,L.core.double,L.skywalkDirectSelectorG,
    L.skywalkDirectSelectorS,L.skywalkDirectZero]

/-- Only the shared labels and twelve declared metadata sites are placed.
Fallback labels outside that domain carry no injectivity claim. -/
def pointIndexWire (L : ControlledPointLayout) (i : Nat) : Wire :=
  if i < 2314 then L.skywalkDirectMap i else (pointMeta L).getD (i-2400) L.control

def pointWireFn (L : ControlledPointLayout) (q : Wire) : Wire := pointIndexWire L (q-16)
def pointIndexSites : List Nat := List.range' 0 2314++List.range' 2400 12

theorem pointWireFn_base (L : ControlledPointLayout) (i : Nat) :
    pointWireFn L (base i) = pointIndexWire L i := by
  simp only [pointWireFn,base,Nat.add_sub_cancel]

theorem pointIndexWire_shared (L : ControlledPointLayout) (i : Nat) (hi : i < 2314) :
    pointIndexWire L i = L.skywalkDirectMap i := by
  simp only [pointIndexWire,if_pos hi]

theorem pointIndexWire_metadata (L : ControlledPointLayout) :
    pointIndexWire L 2400=L.core.generic ∧ pointIndexWire L 2401=L.point.finite ∧
    pointIndexWire L 2402=L.control ∧ pointIndexWire L 2403=L.infinitySelect ∧
    pointIndexWire L 2404=L.doubleSelect ∧ pointIndexWire L 2405=L.genericSelect ∧
    pointIndexWire L 2406=L.core.equalX ∧ pointIndexWire L 2407=L.core.equalNegY ∧
    pointIndexWire L 2408=L.core.double ∧ pointIndexWire L 2409=L.skywalkDirectSelectorG ∧
    pointIndexWire L 2410=L.skywalkDirectSelectorS ∧ pointIndexWire L 2411=L.skywalkDirectZero := by
  simp [pointIndexWire,pointMeta]

private theorem inventory_map (L : ControlledPointLayout) :
    pointIndexSites.map (pointIndexWire L)=skywalkSharedWires L.skywalkDirectMap++pointMeta L := by
  have shared : (List.range' 0 2314).map (pointIndexWire L)=skywalkSharedWires L.skywalkDirectMap := by
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range'_1] at hi
    exact pointIndexWire_shared L i hi.2
  have metadataMap : (List.range' 2400 12).map (pointIndexWire L)=pointMeta L := by
    simp [List.range',pointIndexWire,pointMeta]
  simp only [pointIndexSites,List.map_append,shared,metadataMap]

/-- All2314 shared labels and twelve metadata labels permute exactly the
existing declared point inventory, including its three arithmetic scalars. -/
theorem pointIndexSites_perm (L : ControlledPointLayout) (hw : L.Widths) :
    (pointIndexSites.map (pointIndexWire L)).Perm L.skywalkDirectDeclaredSites := by
  have shared := skywalkPointWire_shared L.core.poolWire L.point.x L.point.y hw.inputX hw.inputY
  have poolPrefix : L.dialogPool.take 1805=wireBlock L.core.poolWire 0 1805 := by
    rw [L.core.pool_prefix hw 1805 (by omega)]
    simp only [dialogPool,List.take_take,Nat.min_eq_left (show 1805≤2613 by omega)]
  have split : wireBlock L.core.poolWire 0 1805=
      wireBlock L.core.poolWire 0 770++wireBlock L.core.poolWire 770 1030++
      wireBlock L.core.poolWire 1800 2++
      [L.skywalkDirectSelectorG,L.skywalkDirectSelectorS,L.skywalkDirectZero] := by
    have scalars : wireBlock L.core.poolWire 1802 3=
        [L.skywalkDirectSelectorG,L.skywalkDirectSelectorS,L.skywalkDirectZero] := by
      simp [wireBlock,List.range',skywalkDirectSelectorG,skywalkDirectSelectorS,skywalkDirectZero]
    rw [←wireBlock_append L.core.poolWire 0 1802 3,scalars]
    have first : wireBlock L.core.poolWire 0 1802=
        wireBlock L.core.poolWire 0 770++wireBlock L.core.poolWire 770 1030++
        wireBlock L.core.poolWire 1800 2 := by
      symm; rw [wireBlock_append,wireBlock_append]
    rw [first]
  rw [inventory_map]
  apply List.perm_iff_count.mpr
  intro q
  simp only [skywalkDirectDeclaredSites,poolPrefix,split,skywalkDirectMap,shared,
    pointMeta,PointAddLayout.pointWires,inPlaceFlags,List.count_append,List.count_cons,List.count_nil]
  omega

private theorem nodup_map_inj (f : Nat → Wire) (xs : List Nat)
    (nd : (xs.map f).Nodup) (a b : Nat) (ha : a∈xs) (hb : b∈xs) (eq : f a=f b) : a=b := by
  induction xs generalizing a b with
  | nil => simp at ha
  | cons c cs ih =>
    have head := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with atHead|inTailA
    · rcases List.mem_cons.mp hb with btHead|inTailB
      · exact atHead.trans btHead.symm
      · have inMap : f b ∈ cs.map f := List.mem_map.mpr ⟨b,inTailB,rfl⟩
        have headEq : f c = f b := (congrArg f atHead).symm.trans eq
        exact (head.1 (headEq.symm ▸ inMap)).elim
    · rcases List.mem_cons.mp hb with btHead|inTailB
      · have inMap : f a ∈ cs.map f := List.mem_map.mpr ⟨a,inTailA,rfl⟩
        have headEq : f a = f c := eq.trans (congrArg f btHead)
        exact (head.1 (headEq ▸ inMap)).elim
      · exact ih head.2 a b inTailA inTailB eq

theorem indices_subset_pointIndexSites : indices ⊆ pointIndexSites := by
  intro i hi
  simp only [indices,pointIndexSites,List.mem_append,List.mem_range'_1] at hi ⊢
  omega

/-- Finite placement injectivity on S only, derived from the declared
point-site permutation. No global Wire→Wire injectivity is asserted. -/
theorem pointWireFn_injective_slots (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ∀ a∈slots.toFinset,∀ b∈slots.toFinset,pointWireFn L a=pointWireFn L b → a=b := by
  have nd := (pointIndexSites_perm L hw).nodup_iff.mpr (L.skywalkDirectDeclaredSites_nodup hn)
  intro a ha b hb eq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  have same : pointIndexWire L i=pointIndexWire L j := by
    simpa only [pointWireFn,Nat.add_sub_cancel] using eq
  have ij := nodup_map_inj (pointIndexWire L) pointIndexSites nd i j
    (indices_subset_pointIndexSites hi) (indices_subset_pointIndexSites hj) same
  exact congrArg (fun k => k+16) ij

theorem pointWireFn_block (L : ControlledPointLayout) (start len : Nat) :
    (wireBlock base start len).map (pointWireFn L)=wireBlock (pointIndexWire L) start len := by
  simp only [wireBlock,List.map_map]
  apply List.map_congr_left
  intro i _
  exact pointWireFn_base L i

theorem pointWireFn_shared_block (L : ControlledPointLayout) (start len : Nat) (bound : start+len≤2314) :
    (wireBlock base start len).map (pointWireFn L)=wireBlock L.skywalkDirectMap start len := by
  rw [pointWireFn_block]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range'_1] at hi
  exact pointIndexWire_shared L i (by omega)

theorem pointWireFn_coordinates (L : ControlledPointLayout) (hw : L.Widths) :
    (wireBlock base 770 256).map (pointWireFn L)=L.point.x ∧
    (wireBlock base 2056 256).map (pointWireFn L)=L.point.y := by
  rw [pointWireFn_shared_block L 770 256 (by omega),
    pointWireFn_shared_block L 2056 256 (by omega)]
  exact L.skywalkDirectMap_coordinates hw

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.pointWireFn_injective_slots
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.pointWireFn_coordinates
