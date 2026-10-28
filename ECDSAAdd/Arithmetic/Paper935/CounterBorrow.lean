import ECDSAAdd.Arithmetic.Paper935.RowAllocation
import ECDSAAdd.Arithmetic.Divsteps.CounterUpdate

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

/-- Public split of a fresh batch into zero source and ripple carries. -/
def planCounterScratch (A : Arena) (width : Nat) :
    Option (Arena × List Wire × List Wire) := do
  let (B,qs) ← A.borrowMany (2*width-1)
  pure (B,qs.take width,qs.drop width)

theorem planCounterScratch_contract (A B : Arena) (width : Nat)
    (zero carry : List Wire) (hw : 1≤width)
    (h : planCounterScratch A width=some (B,zero,carry)) :
    zero.length=width ∧ carry.length+1=width ∧ (zero++carry).Nodup ∧
    A.reserve (zero++carry).toFinset=some B := by
  unfold planCounterScratch at h
  cases hb : A.borrowMany (2*width-1) with
  | none => simp [hb] at h
  | some pair =>
    rcases pair with ⟨C,qs⟩
    simp only [hb] at h
    cases h
    have hc := A.borrowMany_contract C (2*width-1) qs hb
    refine ⟨?_,?_,?_,?_⟩
    · rw [List.length_take,hc.1]; omega
    · rw [List.length_drop,hc.1]; omega
    · simpa only [List.take_append_drop] using hc.2.1
    · simpa only [List.take_append_drop] using hc.2.2

theorem planCounterScratch_capacity (A : Arena) (width : Nat) :
    (∃ B zero carry,planCounterScratch A width=some (B,zero,carry)) ↔
      A.live.card+(2*width-1)≤935 := by
  constructor
  · rintro ⟨B,zero,carry,h⟩
    apply (A.borrowMany_capacity (2*width-1)).mp
    unfold planCounterScratch at h
    cases hb : A.borrowMany (2*width-1) with
    | none => simp [hb] at h
    | some pair => exact ⟨pair.1,pair.2,rfl⟩
  · intro h
    obtain ⟨B,qs,hb⟩ := (A.borrowMany_capacity (2*width-1)).mpr h
    exact ⟨B,qs.take width,qs.drop width,by simp [planCounterScratch,hb]⟩

theorem planCounterScratch_nodup (A B : Arena) (active swap : Wire)
    (z zero carry : List Wire) (hz : 1≤z.length)
    (hn : (active::swap::z).Nodup) (hown : (active::swap::z).toFinset⊆A.live)
    (hplan : planCounterScratch A z.length=some (B,zero,carry)) :
    (active::swap::(zero++z++carry)).Nodup := by
  have hc := planCounterScratch_contract A B z.length zero carry hz hplan
  have hv := (A.reserve_success (zero++carry).toFinset).mp ⟨B,hc.2.2.2⟩
  have full : ((active::swap::z)++(zero++carry)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hn,hc.2.2.1,?_⟩
    intro a ha b hb he
    subst b
    exact Finset.disjoint_left.mp hv.2 (hown (List.mem_toFinset.mpr ha))
      (List.mem_toFinset.mpr hb)
  apply List.nodup_iff_count.mpr
  intro a
  have hh := List.nodup_iff_count.mp full a
  simp only [List.count_append,List.count_cons] at hh ⊢
  omega

theorem counterUpdate_borrowed_support (A B : Arena) (active swap : Wire)
    (z zero carry : List Wire) (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (hown : (active::swap::z).toFinset⊆A.live)
    (hborrow : A.reserve (zero++carry).toFinset=some B) :
    wires (counterUpdate active swap zero z carry)⊆arenaWires := by
  have hv := (A.reserve_success (zero++carry).toFinset).mp ⟨B,hborrow⟩
  refine (counterUpdate_wires_subset active swap zero z carry hz hc).trans ?_
  intro q hq
  have cases : q∈(active::swap::z).toFinset ∨ q∈(zero++carry).toFinset := by
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    tauto
  exact cases.elim (fun h => A.bounded (hown h)) (fun h => hv.1 h)

/-- Counter scratch is borrowed after row shrinkage and returned after the
actual measured ripple update. Its addresses need not be disjoint from the
previous, larger row views. -/
theorem counterUpdate_borrowed (A B : Arena) (active swap : Wire)
    (z zero carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (hown : (active::swap::z).toFinset⊆A.live)
    (hborrow : A.reserve (zero++carry).toFinset=some B)
    (s : State) (m : List Bool) (hr : A.Ready s.basis) :
    let t := run (counterUpdate active swap zero z carry) m s
    t.phase=s.phase ∧ A.Ready t.basis ∧
    regValue z t.basis=counterWord z.length (s.basis active) (s.basis swap) (regValue z s.basis) ∧
    (∀ q,q∉z → t.basis q=s.basis q) ∧
    (∃ C,B.release (zero++carry).toFinset t.basis=some C ∧ C.live=A.live) := by
  have valid := (A.reserve_success (zero++carry).toFinset).mp ⟨B,hborrow⟩
  have fresh := (A.reserve_ready B (zero++carry).toFinset s.basis hr hborrow).2
  have hz0 : regValue zero s.basis=0 := by
    apply (regValue_zero zero s.basis).mpr
    intro q hq
    exact fresh q (by simp [hq])
  have hc0 : regValue carry s.basis=0 := by
    apply (regValue_zero carry s.basis).mpr
    intro q hq
    exact fresh q (by simp [hq])
  have hs := counterUpdate_spec active swap zero z carry hn hz hc
    (s.basis active) (s.basis swap) (regValue z s.basis) s m ⟨rfl,rfl,hz0,rfl,hc0⟩
  have frame := counterUpdate_frame active swap zero z carry hn hz hc s m hz0 hc0
  have live : B.live=A.live∪(zero++carry).toFinset := by
    simp only [Arena.reserve,dif_pos valid,Option.some.injEq] at hborrow
    cases hborrow
    rfl
  have clean : ∀ q∈(zero++carry).toFinset,
      (run (counterUpdate active swap zero z carry) m s).basis q=false := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_append] at hq
    exact hq.elim ((regValue_zero zero _).mp hs.2.2.2.1 q)
      ((regValue_zero carry _).mp hs.2.2.2.2.2 q)
  dsimp only
  refine ⟨hs.1,?_,hs.2.2.2.2.1,frame,?_⟩
  · intro q hq hout
    rw [frame q (fun hm => hout (hown (by simp [hm])))]
    exact hr q hq hout
  · have sub : (zero++carry).toFinset⊆B.live := by rw [live]; exact Finset.subset_union_right
    refine ⟨⟨B.live\(zero++carry).toFinset,Finset.Subset.trans Finset.sdiff_subset B.bounded⟩,?_,?_⟩
    · unfold Arena.release
      split
      · rfl
      · rename_i hn; exact (hn ⟨sub,clean⟩).elim
    · dsimp only
      rw [live]
      ext q
      simp only [Finset.mem_sdiff,Finset.mem_union]
      constructor
      · rintro ⟨hq,hn⟩; exact hq.elim id (fun h => (hn h).elim)
      · intro hq; exact ⟨Or.inl hq,fun hh => Finset.disjoint_left.mp valid.2 hq hh⟩

end ECDSAAdd.Arithmetic.Paper935
