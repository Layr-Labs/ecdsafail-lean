import ECDSAAdd.Arithmetic.Paper935.RowAllocation

namespace ECDSAAdd.Arithmetic.Paper935

structure WindowRow where
  payload : List Wire
  sign : Wire
  deriving DecidableEq, Repr

def WindowRow.wires (r : WindowRow) : List Wire := r.payload++[r.sign]
def WindowRow.value (r : WindowRow) (s : BasisState) : Int := signedRegValue r.wires s

def Arena.retireSet (A : Arena) (qs : Finset Wire) : Arena :=
  ⟨A.live\qs,Finset.Subset.trans Finset.sdiff_subset A.bounded⟩

/-- A public width transition emits actual sign-extension or clearing gates.
Shrinking changes allocation metadata only after the numeric window proof has
established that those gates clear the returned physical sites. -/
def planRowResize (A : Arena) (r : WindowRow) (width : Nat) :
    Option (Arena × WindowRow × Program) :=
  if (r.sign::r.payload).Nodup ∧ (r.sign::r.payload).toFinset⊆A.live then
    if r.payload.length≤width then do
      let (B,qs) ← A.borrowMany (width-r.payload.length)
      pure (B,⟨r.payload++qs,r.sign⟩,growRow r.sign qs)
    else
      let lo := r.payload.take width
      let extra := r.payload.drop width
      some (A.retireSet extra.toFinset,⟨lo,r.sign⟩,shrinkRow r.sign extra)
  else none

theorem planRowResize_correct (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (h : planRowResize A r width=some (B,out,p)) (s : State) (m : List Bool)
    (hr : A.Ready s.basis) (hfit : PayloadFits width (r.value s.basis)) :
    out.payload.length=width ∧ (out.sign::out.payload).Nodup ∧
    (out.sign::out.payload).toFinset⊆B.live ∧ B.Ready (run p m s).basis ∧
    out.value (run p m s).basis=r.value s.basis := by
  unfold planRowResize at h
  split at h
  next valid =>
    split at h
    next grow =>
      cases hb : A.borrowMany (width-r.payload.length) with
      | none => simp [hb] at h
      | some result =>
        rcases result with ⟨C,qs⟩
        simp only [hb] at h
        rcases h with ⟨rfl,rfl,rfl⟩
        have hg := growRow_planned A C r.payload qs r.sign _ valid.1 valid.2 hb s m hr
        have hc := A.borrowMany_contract C _ qs hb
        have hv := (A.reserve_success qs.toFinset).mp ⟨C,hc.2.2⟩
        have hlive : C.live=A.live∪qs.toFinset := by
          have he := hc.2.2
          simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at he
          cases he
          rfl
        refine ⟨?_,hg.2.2.1,?_,hg.2.1,hg.2.2.2⟩
        · simp only [List.length_append,hg.1]
          omega
        · rw [hlive]
          intro q hq
          simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
          rcases hq with hq|hq|hq
          · exact Finset.mem_union_left _ (valid.2 (by simp [hq]))
          · exact Finset.mem_union_left _ (valid.2 (by simp [hq]))
          · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hq)
    next shrink =>
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      let lo := r.payload.take width
      let extra := r.payload.drop width
      have heq : lo++extra=r.payload := List.take_append_drop width r.payload
      have hn : (r.sign::(lo++extra)).Nodup := by rw [heq]; exact valid.1
      have own : extra.toFinset⊆A.live := by
        intro q hq
        exact valid.2 (by simp only [List.mem_toFinset,List.mem_cons]; exact Or.inr (List.mem_of_mem_drop (List.mem_toFinset.mp hq)))
      have hlen : lo.length=width := by
        simp only [lo,List.length_take,Nat.min_eq_left (by omega : width≤r.payload.length)]
      have fits : PayloadFits lo.length (signedRegValue ((lo++extra)++[r.sign]) s.basis) := by
        rw [hlen,heq]
        exact hfit
      obtain ⟨C,hC,hready,hvalue⟩ := shrinkRow_release A lo extra r.sign hn s m hr own fits
      have hCeq : C=A.retireSet extra.toFinset := by
        unfold Arena.release at hC
        split at hC
        · cases hC; rfl
        · simp at hC
      subst C
      refine ⟨hlen,?_,?_,hready,hvalue.trans (by rw [heq]; rfl)⟩
      · have hn' := valid.1
        exact List.Pairwise.sublist (by simp only [List.cons_sublist_cons]; exact List.take_sublist width r.payload) hn'
      · intro q hq
        apply Finset.mem_sdiff.mpr
        have hlo : q∈r.sign::lo := List.mem_toFinset.mp hq
        refine ⟨valid.2 (List.mem_toFinset.mpr ?_),?_⟩
        · rcases List.mem_cons.mp hlo with hq|hq
          · exact List.mem_cons.mpr (Or.inl hq)
          · exact List.mem_cons_of_mem _ (List.mem_of_mem_take hq)
        · intro hex
          have hd := (List.nodup_append.mp (show ((r.sign::lo)++extra).Nodup from hn)).2.2
          exact hd q hlo q (List.mem_toFinset.mp hex) rfl
  next invalid => simp at h

theorem planRowResize_locality (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (h : planRowResize A r width=some (B,out,p)) (s : State) (m : List Bool) :
    ∀ w∈A.live,w∉r.wires → w∈B.live ∧ (run p m s).basis w=s.basis w := by
  unfold planRowResize at h
  split at h
  next valid =>
    split at h
    next grow =>
      cases hb : A.borrowMany (width-r.payload.length) with
      | none => simp [hb] at h
      | some result =>
        rcases result with ⟨C,qs⟩
        simp only [hb] at h
        rcases h with ⟨rfl,rfl,rfl⟩
        have hc := A.borrowMany_contract C _ qs hb
        have hv := (A.reserve_success qs.toFinset).mp ⟨C,hc.2.2⟩
        have hlive : C.live=A.live∪qs.toFinset := by
          have he := hc.2.2
          simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at he
          cases he
          rfl
        intro w hw _
        refine ⟨by rw [hlive]; exact Finset.mem_union_left _ hw,?_⟩
        exact (growRow_frame r.sign qs s m).2 w
          (fun hq => Finset.disjoint_left.mp hv.2 hw (List.mem_toFinset.mpr hq))
    next shrink =>
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      intro w hw hout
      have hex : w∉r.payload.drop width := by
        intro hh
        exact hout (List.mem_append_left _ (List.mem_of_mem_drop hh))
      exact ⟨Finset.mem_sdiff.mpr ⟨hw,by simpa using hex⟩,(shrinkRow_frame r.sign _ s m).2 w hex⟩
  next invalid => simp at h

theorem planRowResize_resources (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (h : planRowResize A r width=some (B,out,p)) :
    ProperProgram p ∧ toffoliCount p=0 ∧ measurementCount p=0 ∧ wires p⊆arenaWires := by
  unfold planRowResize at h
  split at h
  next valid =>
    split at h
    next grow =>
      cases hb : A.borrowMany (width-r.payload.length) with
      | none => simp [hb] at h
      | some result =>
        rcases result with ⟨C,qs⟩
        simp only [hb] at h
        rcases h with ⟨rfl,rfl,rfl⟩
        have hc := A.borrowMany_contract C _ qs hb
        have hv := (A.reserve_success qs.toFinset).mp ⟨C,hc.2.2⟩
        have hs : r.sign∈A.live := valid.2 (by simp)
        have hn : r.sign∉qs := fun hq => Finset.disjoint_left.mp hv.2 hs (List.mem_toFinset.mpr hq)
        refine ⟨growRow_proper _ _ hn,(rowWindow_cost _ _).1,(rowWindow_cost _ _).2.1,?_⟩
        intro w hw
        have hmem := growRow_support r.sign qs hw
        rcases Finset.mem_insert.mp hmem with hmem|hmem
        · subst w; exact A.bounded hs
        · exact hv.1 hmem
    next shrink =>
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      have hn : r.sign∉r.payload.drop width := fun hq =>
        (List.nodup_cons.mp valid.1).1 (List.mem_of_mem_drop hq)
      rw [shrinkRow_eq]
      refine ⟨growRow_proper _ _ (by simpa using hn),(rowWindow_cost _ _).1,(rowWindow_cost _ _).2.1,?_⟩
      intro w hw
      have hmem := growRow_support r.sign (r.payload.drop width).reverse hw
      apply A.bounded
      apply valid.2
      simp only [List.mem_toFinset,List.mem_cons]
      rcases Finset.mem_insert.mp hmem with hmem|hmem
      · exact Or.inl hmem
      · exact Or.inr (List.mem_of_mem_drop (List.mem_reverse.mp (List.mem_toFinset.mp hmem)))
  next invalid => simp at h

theorem planRowResize_old_sites (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (h : planRowResize A r width=some (B,out,p)) :
    ∀ w∈out.wires,w∈A.live → w∈r.wires := by
  unfold planRowResize at h
  split at h
  next valid =>
    split at h
    next grow =>
      cases hb : A.borrowMany (width-r.payload.length) with
      | none => simp [hb] at h
      | some result =>
        rcases result with ⟨C,qs⟩
        simp only [hb] at h
        rcases h with ⟨rfl,rfl,rfl⟩
        have hc := A.borrowMany_contract C _ qs hb
        have hv := (A.reserve_success qs.toFinset).mp ⟨C,hc.2.2⟩
        intro w hw ha
        simp only [WindowRow.wires,List.mem_append,List.mem_singleton] at hw ⊢
        rcases hw with (hw|hw)|hw
        · exact Or.inl hw
        · exact False.elim (Finset.disjoint_left.mp hv.2 ha (List.mem_toFinset.mpr hw))
        · exact Or.inr hw
    next shrink =>
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      intro w hw _
      simp only [WindowRow.wires,List.mem_append,List.mem_singleton] at hw ⊢
      exact hw.elim (fun h => Or.inl (List.mem_of_mem_take h)) Or.inr
  next invalid => simp at h

/-- Public compilation cannot fail when the row is owned and the requested
new payload bits fit the remaining physical arena. -/
theorem planRowResize_exists (A : Arena) (r : WindowRow) (width : Nat)
    (hn : (r.sign::r.payload).Nodup) (hown : (r.sign::r.payload).toFinset⊆A.live)
    (hcap : A.live.card+(width-r.payload.length)≤935) :
    ∃ B out p,planRowResize A r width=some (B,out,p) := by
  unfold planRowResize
  rw [if_pos ⟨hn,hown⟩]
  split
  next hg =>
    obtain ⟨B,qs,hb⟩ := (A.borrowMany_capacity (width-r.payload.length)).mpr hcap
    refine ⟨B,⟨r.payload++qs,r.sign⟩,growRow r.sign qs,?_⟩
    simp [hb]
  next hg => exact ⟨_,_,_,rfl⟩

theorem planRowResize_live_bound (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (h : planRowResize A r width=some (B,out,p)) :
    B.live.card≤A.live.card+(width-r.payload.length) := by
  unfold planRowResize at h
  split at h
  next valid =>
    split at h
    next grow =>
      cases hb : A.borrowMany (width-r.payload.length) with
      | none => simp [hb] at h
      | some result =>
        rcases result with ⟨C,qs⟩
        simp only [hb] at h
        cases h
        have hc := A.borrowMany_contract C _ qs hb
        have hv := (A.reserve_success qs.toFinset).mp ⟨C,hc.2.2⟩
        have live : C.live=A.live∪qs.toFinset := by
          have hh := hc.2.2
          simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at hh
          cases hh
          rfl
        rw [live,Finset.card_union_of_disjoint hv.2,List.toFinset_card_of_nodup hc.2.1,hc.1]
    next shrink =>
      cases h
      exact le_trans (Finset.card_le_card Finset.sdiff_subset) (Nat.le_add_right _ _)
  next invalid => simp at h

end ECDSAAdd.Arithmetic.Paper935
