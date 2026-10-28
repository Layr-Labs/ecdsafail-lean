import ECDSAAdd.Arithmetic.SkywalkShared

namespace ECDSAAdd.Arithmetic

/-- Overlay the existing caller coordinate words on the shared port, using
1,802 positions from its clean workspace for all other sites. -/
def skywalkPointWire (pool : Nat → Wire) (x y : List Wire) (i : Nat) : Wire :=
  if 770 ≤ i ∧ i < 1026 then x.getD (i-770) 0
  else if 2056 ≤ i ∧ i < 2312 then y.getD (i-2056) 0
  else pool (i-(if 1026 ≤ i then 256 else 0)-(if 2312 ≤ i then 256 else 0))

private theorem point_getD_range (xs : List Wire) (n : Nat) (hn : xs.length=n) :
    (List.range n).map (fun i => xs.getD i 0)=xs := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem _ _ hj

theorem skywalkPointWire_x (pool : Nat → Wire) (x y : List Wire) (hx : x.length=256) :
    wireBlock (skywalkPointWire pool x y) 770 256=x := by
  rw [wireBlock,List.range'_eq_map_range,List.map_map]
  have he : (List.range 256).map (fun i => skywalkPointWire pool x y (770+i))=
      (List.range 256).map (fun i => x.getD i 0) := by
    apply List.map_congr_left
    intro i hi
    have hb := List.mem_range.mp hi
    simp [skywalkPointWire,show 770 ≤ 770+i ∧ 770+i < 1026 by omega]
  exact he.trans (point_getD_range x 256 hx)

theorem skywalkPointWire_y (pool : Nat → Wire) (x y : List Wire) (hy : y.length=256) :
    wireBlock (skywalkPointWire pool x y) 2056 256=y := by
  rw [wireBlock,List.range'_eq_map_range,List.map_map]
  have he : (List.range 256).map (fun i => skywalkPointWire pool x y (2056+i))=
      (List.range 256).map (fun i => y.getD i 0) := by
    apply List.map_congr_left
    intro i hi
    have hb := List.mem_range.mp hi
    simp [skywalkPointWire,show ¬(770 ≤ 2056+i ∧ 2056+i < 1026) by omega,
      show 2056 ≤ 2056+i ∧ 2056+i < 2312 by omega]
  exact he.trans (point_getD_range y 256 hy)

private theorem point_prefix (pool : Nat → Wire) (x y : List Wire) :
    wireBlock (skywalkPointWire pool x y) 0 770=wireBlock pool 0 770 := by
  simp only [wireBlock,List.range'_eq_map_range,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hb := List.mem_range.mp hi
  simp only [Function.comp_def,Nat.zero_add]
  change skywalkPointWire pool x y i=pool i
  simp [skywalkPointWire,show ¬(770 ≤ i ∧ i < 1026) by omega,
    show ¬(2056 ≤ i ∧ i < 2312) by omega,
    show ¬1026 ≤ i by omega,show ¬2312 ≤ i by omega]

private theorem point_middle (pool : Nat → Wire) (x y : List Wire) :
    wireBlock (skywalkPointWire pool x y) 1026 1030=wireBlock pool 770 1030 := by
  simp only [wireBlock,List.range'_eq_map_range,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hb := List.mem_range.mp hi
  have hid : 1026+i-256=770+i := by omega
  simp [skywalkPointWire,show ¬(2056 ≤ 1026+i ∧ 1026+i < 2312) by omega,
    show 1026 ≤ 1026+i by omega,show ¬2312 ≤ 1026+i by omega,hid]

private theorem point_suffix (pool : Nat → Wire) (x y : List Wire) :
    wireBlock (skywalkPointWire pool x y) 2312 2=wireBlock pool 1800 2 := by
  simp only [wireBlock,List.range'_eq_map_range,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hb := List.mem_range.mp hi
  have hid : 2312+i-256-256=1800+i := by omega
  simp [skywalkPointWire,show ¬(770 ≤ 2312+i ∧ 2312+i < 1026) by omega,
    show 1026 ≤ 2312+i by omega,show 2312 ≤ 2312+i by omega,hid]

theorem skywalkPointWire_shared (pool : Nat → Wire) (x y : List Wire)
    (hx : x.length=256) (hy : y.length=256) :
    skywalkSharedWires (skywalkPointWire pool x y)=
      wireBlock pool 0 770++x++wireBlock pool 770 1030++y++wireBlock pool 1800 2 := by
  have hblocks : wireBlock (skywalkPointWire pool x y) 0 2314=
      wireBlock (skywalkPointWire pool x y) 0 770++
      wireBlock (skywalkPointWire pool x y) 770 256++
      wireBlock (skywalkPointWire pool x y) 1026 1030++
      wireBlock (skywalkPointWire pool x y) 2056 256++
      wireBlock (skywalkPointWire pool x y) 2312 2 := by
    symm
    rw [wireBlock_append,wireBlock_append,wireBlock_append,wireBlock_append]
  simpa only [skywalkSharedWires,point_prefix,skywalkPointWire_x pool x y hx,
    point_middle,skywalkPointWire_y pool x y hy,point_suffix] using hblocks

theorem skywalkPointWire_nodup (pool : Nat → Wire) (x y : List Wire)
    (hx : x.length=256) (hy : y.length=256)
    (hn : (wireBlock pool 0 1802++x++y).Nodup) :
    (skywalkSharedWires (skywalkPointWire pool x y)).Nodup := by
  rw [skywalkPointWire_shared pool x y hx hy]
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hn q
  have hp : wireBlock pool 0 1802=wireBlock pool 0 770++
      wireBlock pool 770 1030++wireBlock pool 1800 2 := by
    symm
    rw [wireBlock_append,wireBlock_append]
  rw [hp] at hh
  simp only [List.count_append] at hh ⊢
  omega

/-- The overlay has precisely the two caller words and its clean workspace.
This statement is about physical support, with no lifetime assumptions. -/
theorem skywalkPointWire_mem (pool : Nat → Wire) (x y : List Wire)
    (hx : x.length=256) (hy : y.length=256) (q : Wire) :
    q∈skywalkSharedWires (skywalkPointWire pool x y) ↔
      q∈wireBlock pool 0 1802 ∨ q∈x ∨ q∈y := by
  have hp : wireBlock pool 0 1802=wireBlock pool 0 770++
      wireBlock pool 770 1030++wireBlock pool 1800 2 := by
    symm
    rw [wireBlock_append,wireBlock_append]
  rw [skywalkPointWire_shared pool x y hx hy,hp]
  simp only [List.mem_append]
  tauto

/-- Clean caller workspace supplies every zero required by the shared port,
even when the two coordinate words contain arbitrary canonical field values. -/
theorem skywalkPointWire_clean (pool : Nat → Wire) (x y : List Wire)
    (hx : x.length=256) (hy : y.length=256) (s : BasisState)
    (hc : regValue (wireBlock pool 0 1802) s=0) :
    ∀ q∈skywalkSharedWires (skywalkPointWire pool x y),q∉x → q∉y → s q=false := by
  intro q hq hqx hqy
  have hmem := (skywalkPointWire_mem pool x y hx hy q).mp hq
  rcases hmem with hp|hxx|hyy
  · exact (regValue_zero _ _).mp hc q hp
  · exact False.elim (hqx hxx)
  · exact False.elim (hqy hyy)

/-- A caller control separated from the physical caller words and workspace
is also outside the entire shared arithmetic universe. -/
theorem skywalkPointWire_control_outside (pool : Nat → Wire) (x y : List Wire)
    (hx : x.length=256) (hy : y.length=256) (control : Wire)
    (hn : (control::wireBlock pool 0 1802++x++y).Nodup) :
    control∉skywalkSharedWires (skywalkPointWire pool x y) := by
  intro hmem
  have hnot := (List.nodup_cons.mp hn).1
  rcases (skywalkPointWire_mem pool x y hx hy control).mp hmem with hp|hxx|hyy
  · exact hnot (List.mem_append_left _ (List.mem_append_left _ hp))
  · exact hnot (List.mem_append_left _ (List.mem_append_right _ hxx))
  · exact hnot (List.mem_append_right _ hyy)

end ECDSAAdd.Arithmetic
