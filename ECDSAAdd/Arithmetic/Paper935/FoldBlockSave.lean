import ECDSAAdd.Arithmetic.Paper935.FoldPoolPlan
import ECDSAAdd.Arithmetic.Paper935.Repack

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Retain the final block carry, then swap it into a cleared pool slot. -/
def foldBlockSave (control top save : Wire) (cells : List FoldCell) (cin : Option Wire) : Program :=
  foldBlock control cells cin true true ++ rehome top save

/-- The first carry slot may be reused as keeper storage once the backward
sweep has erased it. No extra fresh keeper wire is required. -/
theorem foldBlockSave_run (control top : Wire) (saved : FoldCell) (cells : List FoldCell) (cin : Option Wire)
    (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (hs : saved∈cells) (hTop : foldBlockTop cells cin=some top) (different : top≠saved.carry)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false) :
    run (foldBlockSave control top saved.carry cells cin) m s=
      ⟨s.phase,writeBit (writeBit (foldBlockModel control cells cin true true s.basis) top false) saved.carry
        (foldBlockOverflow cells (s.basis control) ((cin.map s.basis).getD false) s.basis)⟩ := by
  let basis := foldBlockModel control cells cin true true s.basis
  have savedClean : basis saved.carry=false := by
    apply foldBlockModel_carry_clean control cells cin true true hn s.basis saved hs
    right
    rw [hTop]
    intro h
    exact different (Option.some.inj h)
  have topValue : basis top=foldBlockOverflow cells (s.basis control) ((cin.map s.basis).getD false) s.basis := by
    simpa only [hTop,Option.map_some,Option.getD_some] using foldBlockModel_top control cells cin hn s.basis
  rw [foldBlockSave,run_append,run_take,foldBlock_run control cells cin true true hn s m clean]
  have moved := rehome_run top saved.carry different ⟨s.phase,basis⟩
    (m.drop (measurementCount (foldBlock control cells cin true true)))
  apply congrArg₂ State.mk
  · exact moved.1
  · funext q
    have value := moved.2 (Equiv.swap top saved.carry q)
    simp only [Equiv.swap_apply_self] at value
    change (run (rehome top saved.carry) (m.drop (measurementCount (foldBlock control cells cin true true)))
      ⟨s.phase,basis⟩).basis q=_
    rw [value]
    by_cases ht : q=top <;> by_cases hs : q=saved.carry <;>
      simp_all [Equiv.swap_apply_def,writeBit,Function.update,basis]

theorem foldBlockSave_carries (control top : Wire) (saved : FoldCell) (cells : List FoldCell) (cin : Option Wire)
    (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (hs : saved∈cells) (hTop : foldBlockTop cells cin=some top) (different : top≠saved.carry)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false)
    (cell : FoldCell) (hc : cell∈cells) :
    (run (foldBlockSave control top saved.carry cells cin) m s).basis cell.carry=
      if cell.carry=saved.carry then
        foldBlockOverflow cells (s.basis control) ((cin.map s.basis).getD false) s.basis else false := by
  rw [foldBlockSave_run control top saved cells cin hn hs hTop different s m clean]
  by_cases hsave : cell.carry=saved.carry
  · simp [writeBit,Function.update,hsave]
  · by_cases htop : cell.carry=top
    · simp [writeBit,Function.update,htop,different]
    · have erased := foldBlockModel_carry_clean control cells cin true true hn s.basis cell hc
        (Or.inr (by rw [hTop]; intro h; exact htop (Option.some.inj h).symm))
      simpa only [writeBit,Function.update_of_ne hsave,Function.update_of_ne htop,if_neg hsave] using erased

private theorem top_carry_mem (cells : List FoldCell) (cin : Option Wire) (q : Wire)
    (nonempty : cells≠[]) (h : foldBlockTop cells cin=some q) : q∈cells.map FoldCell.carry := by
  induction cells generalizing cin with
  | nil => contradiction
  | cons b rest ih =>
    cases rest with
    | nil =>
      cases hi : cin <;> cases hb : b.literal <;>
        simp [foldBlockTop,FoldCell.next,hi,hb] at h <;> simp [←h]
    | cons c cs =>
      have mem := ih (b.next cin) (by simp) (by simpa only [foldBlockTop] using h)
      exact List.mem_cons_of_mem b.carry mem

private theorem data_carry_disjoint (cells : List FoldCell) (hn : (cells.flatMap FoldCell.wires).Nodup) :
    List.Disjoint (cells.map FoldCell.data) (cells.map FoldCell.carry) := by
  have counts (q : Wire) : (cells.flatMap FoldCell.wires).count q=
      (cells.map FoldCell.data).count q+(cells.map FoldCell.carry).count q := by
    clear hn
    induction cells with
    | nil => rfl
    | cons b rest ih =>
      simp only [List.flatMap_cons,FoldCell.wires,List.map_cons,List.count_append,List.count_cons,List.count_nil,ih]
      omega
  apply List.disjoint_left.mpr
  intro q hd hc
  have h := List.nodup_iff_count.mp hn q
  rw [counts] at h
  have hdata := List.count_pos_iff.mpr hd
  have hcarry := List.count_pos_iff.mpr hc
  omega

theorem foldBlockSave_value (control top : Wire) (saved : FoldCell) (cells : List FoldCell) (cin : Option Wire)
    (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (hs : saved∈cells) (hTop : foldBlockTop cells cin=some top) (different : top≠saved.carry)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false) :
    regValue (cells.map FoldCell.data) (run (foldBlockSave control top saved.carry cells cin) m s).basis=
      (regValue (cells.map FoldCell.data) s.basis+foldBlockLiteral cells (s.basis control)+
        ((cin.map s.basis).getD false).toNat)%2^cells.length := by
  rw [foldBlockSave_run control top saved cells cin hn hs hTop different s m clean]
  have apart := data_carry_disjoint cells (List.nodup_append.mp hn).2.1
  have topMem := top_carry_mem cells cin top (by intro e; simp [e] at hs) hTop
  rw [regValue_congr (cells.map FoldCell.data) _ (foldBlockModel control cells cin true true s.basis) (by
    intro q hq
    have ht : q≠top := by intro e; subst q; exact List.disjoint_left.mp apart hq topMem
    have hsave : q≠saved.carry := by
      intro e; subst q
      exact List.disjoint_left.mp apart hq (List.mem_map.mpr ⟨saved,hs,rfl⟩)
    simp only [writeBit,Function.update_of_ne ht,Function.update_of_ne hsave])]
  exact foldBlockModel_value control cells cin true hn s.basis

theorem foldBlockSave_frame (control top : Wire) (saved : FoldCell) (cells : List FoldCell) (cin : Option Wire)
    (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (hs : saved∈cells) (hTop : foldBlockTop cells cin=some top) (different : top≠saved.carry)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false)
    (q : Wire) (hq : q∉cells.flatMap FoldCell.wires) :
    (run (foldBlockSave control top saved.carry cells cin) m s).basis q=s.basis q := by
  have ht : q≠top := by
    intro e; subst q
    obtain ⟨b,hb,e⟩ := List.mem_map.mp (top_carry_mem cells cin top (by intro e; simp [e] at hs) hTop)
    apply hq
    exact List.mem_flatMap.mpr ⟨b,hb,by simp [FoldCell.wires,e]⟩
  have hsave : q≠saved.carry := by
    intro e; subst q
    exact hq (List.mem_flatMap.mpr ⟨saved,hs,by simp [FoldCell.wires]⟩)
  rw [foldBlockSave_run control top saved cells cin hn hs hTop different s m clean]
  simp only [writeBit,Function.update_of_ne ht,Function.update_of_ne hsave]
  exact foldBlockModel_frame control cells cin true true s.basis q hq

/-- The moved keeper still satisfies the borrow predicate on the written
sum, so the same physical eraser can consume it after later blocks. -/
theorem foldBlockSave_keeper (control top : Wire) (saved : FoldCell) (cells : List FoldCell) (cin : Option Wire)
    (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (hs : saved∈cells) (hTop : foldBlockTop cells cin=some top) (different : top≠saved.carry)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false)
    (inactive : s.basis control=false → (cin.map s.basis).getD false=false) :
    let out := run (foldBlockSave control top saved.carry cells cin) m s
    out.basis saved.carry=(s.basis control && decide
      (regValue (cells.map FoldCell.data) out.basis<foldBlockLiteral cells true+
        ((cin.map s.basis).getD false).toNat)) := by
  dsimp only
  rw [foldBlockSave_carries control top saved cells cin hn hs hTop different s m clean saved hs,if_pos rfl,
    foldBlockSave_value control top saved cells cin hn hs hTop different s m clean]
  have overflow : foldBlockOverflow cells (s.basis control) ((cin.map s.basis).getD false) s.basis=
      decide (2^cells.length≤regValue (cells.map FoldCell.data) s.basis+
        foldBlockLiteral cells (s.basis control)+((cin.map s.basis).getD false).toNat) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using foldBlockOverflow_iff cells (s.basis control) ((cin.map s.basis).getD false) s.basis
  rw [overflow]
  have lit : foldBlockLiteral cells (s.basis control)=
      (if s.basis control then foldBlockLiteral cells true else 0) := by
    cases s.basis control <;> simp [foldBlockLiteral_disabled]
  rw [lit]
  exact foldKeeper_controlled cells.length (regValue (cells.map FoldCell.data) s.basis)
    (foldBlockLiteral cells true) (s.basis control) ((cin.map s.basis).getD false)
    (by simpa only [List.length_map] using regValue_lt (cells.map FoldCell.data) s.basis)
    (foldBlockLiteral_bound cells true) inactive

end ECDSAAdd.Arithmetic.Paper935
