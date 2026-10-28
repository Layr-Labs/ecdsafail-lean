import ECDSAAdd.Arithmetic.UnaryMod

namespace ECDSAAdd.Arithmetic
open ExternalMod

theorem unaryModXor_wires (L : ModLayout) (f : ModField) (operation : Program)
    (hop : wires operation = L.activeWires.toFinset) (src dst : List Wire)
    (hs : src.length=L.width+1) (hd : dst.length=L.width+1) :
    wires (unaryModXor L f operation src dst) = (src ++ dst ++ L.wires).toFinset := by
  have hc := copyRegister_wires none src (L.reg f) (by rw [L.reg_length]; exact hs)
  have ho := copyRegister_wires none L.out dst (by rw [ModLayout.out,L.reg_length]; exact hd.symm)
  have hn : src.isEmpty=false := by cases src <;> simp_all
  have hon : L.out.isEmpty=false := by
    have hh := L.reg_length .out
    cases he : L.out with
    | nil => change L.out.length = _ at hh; rw [he] at hh; simp at hh
    | cons b bs => rfl
  simp only [unaryModXor,wires_append,hc,ho,hop,hn,hon,Bool.false_eq_true,if_false,
    Option.toList_none,List.nil_append]
  ext w
  have hf : w∈L.reg f → w∈L.wires := fun h => field_subset L f h
  have hall : w∈L.activeWires ∨ w∈L.out ↔ w∈L.wires := by
    simpa only [Finset.mem_union,List.mem_toFinset] using
      (show w ∈ L.activeWires.toFinset ∪ L.out.toFinset ↔ w ∈ L.wires.toFinset by rw [modActive_output])
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_append]
  clear hs hd hc ho hn hon hop
  tauto

theorem unaryModXor_counts (L : ModLayout) (f : ModField) (operation : Program)
    (src dst : List Wire) (hs : src.length=L.width+1) (hd : dst.length=L.width+1) :
    toffoliCount (unaryModXor L f operation src dst)=2*toffoliCount operation ∧
    measurementCount (unaryModXor L f operation src dst)=2*measurementCount operation := by
  have hc := copyRegister_counts none src (L.reg f) (by rw [L.reg_length]; exact hs)
  have ho := copyRegister_counts none L.out dst (by rw [ModLayout.out,L.reg_length]; exact hd.symm)
  simp only [unaryModXor,toffoliCount_append,measurementCount_append,hc.1,hc.2,ho.1,ho.2,
    Option.isSome_none,Bool.false_eq_true,if_false]
  omega

theorem reduceXor_wires (L : ModLayout) (src dst : List Wire) (q : Nat)
    (hs : src.length=L.width+1) (hd : dst.length=L.width+1) :
    wires (reduceXor L q src dst)=(src++dst++L.wires).toFinset :=
  unaryModXor_wires L .x (modAdd L q) (modAdd_wires L q) src dst hs hd

theorem negateXor_wires (L : ModLayout) (src dst : List Wire) (q : Nat)
    (hs : src.length=L.width+1) (hd : dst.length=L.width+1) :
    wires (negateXor L q src dst)=(src++dst++L.wires).toFinset :=
  unaryModXor_wires L .y (modSub L q) (modSub_wires L q) src dst hs hd

theorem reduceXor_correct (L : ModLayout) (src dst : List Wire)
    (hnd : (src ++ dst ++ L.wires).Nodup) (hs : src.length = L.width+1)
    (hd : dst.length = L.width+1) (q : Nat) (hq0 : 0 < q) (hq : q < 2^L.width)
    (s : State) (m : List Bool) (hX : regValue src s.basis < 2*q)
    (hw : regValue L.wires s.basis = 0) :
    (run (reduceXor L q src dst) m s).phase = s.phase ∧
    (∀ w, w ∉ dst → (run (reduceXor L q src dst) m s).basis w = s.basis w) ∧
    regValue dst (run (reduceXor L q src dst) m s).basis = regValue dst s.basis ^^^
      (regValue src s.basis % q) := by
  obtain ⟨hp, h⟩ := reduceXor_spec L src dst hnd hs hd q _ _ hq0 hq hX s m ⟨⟨rfl, rfl⟩, hw⟩
  refine ⟨hp, ?_, h.1.2⟩
  intro w hn
  by_cases hsrc : w ∈ src
  · exact (regValue_eq_iff _ _ _).mp h.1.1 w hsrc
  by_cases hL : w ∈ L.wires
  · exact ((regValue_zero _ _).mp h.2 w hL).trans ((regValue_zero _ _).mp hw w hL).symm
  · apply run_preserves_outside
    rw [reduceXor_wires L src dst q hs hd]
    simpa only [List.mem_toFinset, List.mem_append, not_or] using ⟨⟨hsrc, hn⟩, hL⟩


theorem negateXor_correct (L : ModLayout) (src dst : List Wire)
    (hnd : (src ++ dst ++ L.wires).Nodup) (hs : src.length = L.width+1)
    (hd : dst.length = L.width+1) (q : Nat) (hq0 : 0 < q) (hq : q < 2^L.width)
    (s : State) (m : List Bool) (hX : regValue src s.basis < q)
    (hw : regValue L.wires s.basis = 0) :
    (run (negateXor L q src dst) m s).phase = s.phase ∧
    (∀ w, w ∉ dst → (run (negateXor L q src dst) m s).basis w = s.basis w) ∧
    regValue dst (run (negateXor L q src dst) m s).basis = regValue dst s.basis ^^^
      ((q - regValue src s.basis)%q) := by
  obtain ⟨hp, h⟩ := negateXor_spec L src dst hnd hs hd q _ _ hq0 hq hX s m ⟨⟨rfl, rfl⟩, hw⟩
  refine ⟨hp, ?_, h.1.2⟩
  intro w hn
  by_cases hsrc : w ∈ src
  · exact (regValue_eq_iff _ _ _).mp h.1.1 w hsrc
  by_cases hL : w ∈ L.wires
  · exact ((regValue_zero _ _).mp h.2 w hL).trans ((regValue_zero _ _).mp hw w hL).symm
  · apply run_preserves_outside
    rw [negateXor_wires L src dst q hs hd]
    simpa only [List.mem_toFinset, List.mem_append, not_or] using ⟨⟨hsrc, hn⟩, hL⟩


end ECDSAAdd.Arithmetic
