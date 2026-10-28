import ECDSAAdd.Arithmetic.Paper935.RowWindowResize
import ECDSAAdd.Arithmetic.Paper935.Borrow

namespace ECDSAAdd.Arithmetic.Paper935

/-- Select a public batch of least free physical sites; no basis data enter
this compiler choice. The entire batch is reserved before sign extension. -/
def Arena.borrowMany (A : Arena) (n : Nat) : Option (Arena × List Wire) :=
  let free := (arenaWires\A.live).sort (·≤·)
  if n≤free.length then
    let qs := free.take n
    (A.reserve qs.toFinset).map (fun B => (B,qs))
  else none

theorem Arena.borrowMany_contract (A B : Arena) (n : Nat) (qs : List Wire)
    (h : A.borrowMany n=some (B,qs)) :
    qs.length=n ∧ qs.Nodup ∧ A.reserve qs.toFinset=some B := by
  unfold borrowMany at h
  dsimp only at h
  split at h
  next hn =>
    cases hr : A.reserve (((arenaWires\A.live).sort (·≤·)).take n).toFinset with
    | none => simp [hr] at h
    | some C =>
      simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨by rw [List.length_take,Nat.min_eq_left hn],
        ((arenaWires\A.live).sort_nodup (·≤·)).take,hr⟩
  next hn => simp at h

theorem Arena.borrowMany_capacity (A : Arena) (n : Nat) :
    (∃ B qs,A.borrowMany n=some (B,qs)) ↔ A.live.card+n≤935 := by
  let free := (arenaWires\A.live).sort (·≤·)
  have hlen : free.length=935-A.live.card := by
    simp only [free,Finset.length_sort,Finset.card_sdiff_of_subset A.bounded]
    simp [arenaWires]
  have hcap := A.peak_bound
  constructor
  · rintro ⟨B,qs,h⟩
    unfold borrowMany at h
    dsimp only at h
    split at h
    next hn => change n≤free.length at hn; rw [hlen] at hn; omega
    next hn => simp at h
  · intro hn
    have hnf : n≤free.length := by rw [hlen]; omega
    have hsub : (free.take n).toFinset⊆arenaWires := by
      intro q hq
      have hm := List.mem_of_mem_take (List.mem_toFinset.mp hq)
      have hf : q∈arenaWires\A.live := by simpa [free] using hm
      exact (Finset.mem_sdiff.mp hf).1
    have hdis : Disjoint A.live (free.take n).toFinset := by
      apply Finset.disjoint_left.mpr
      intro q hq ht
      have hm := List.mem_of_mem_take (List.mem_toFinset.mp ht)
      have hf : q∈arenaWires\A.live := by simpa [free] using hm
      exact (Finset.mem_sdiff.mp hf).2 hq
    obtain ⟨B,hB⟩ := (A.reserve_success (free.take n).toFinset).mpr ⟨hsub,hdis⟩
    refine ⟨B,free.take n,?_⟩
    change (if n≤free.length then (A.reserve (free.take n).toFinset).map (fun B => (B,free.take n)) else none)=some (B,free.take n)
    rw [if_pos hnf,hB]
    rfl

theorem growRow_planned (A B : Arena) (lo qs : List Wire) (sign : Wire) (n : Nat)
    (hn : (sign::lo).Nodup) (hown : (sign::lo).toFinset⊆A.live)
    (hplan : A.borrowMany n=some (B,qs)) (s : State) (m : List Bool) (hr : A.Ready s.basis) :
    qs.length=n ∧ B.Ready (run (growRow sign qs) m s).basis ∧
    (sign::(lo++qs)).Nodup ∧
    signedRegValue ((lo++qs)++[sign]) (run (growRow sign qs) m s).basis=
      signedRegValue (lo++[sign]) s.basis := by
  have hc := A.borrowMany_contract B n qs hplan
  have hv := (A.reserve_success qs.toFinset).mp ⟨B,hc.2.2⟩
  have ready := A.reserve_ready B qs.toFinset s.basis hr hc.2.2
  have distinct : (sign::(lo++qs)).Nodup := by
    change ((sign::lo)++qs).Nodup
    apply List.nodup_append.mpr
    refine ⟨hn,hc.2.1,?_⟩
    intro a ha b hb he
    subst b
    exact Finset.disjoint_left.mp hv.2 (hown (List.mem_toFinset.mpr ha)) (List.mem_toFinset.mpr hb)
  have hlive : B.live=A.live∪qs.toFinset := by
    have he := hc.2.2
    simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at he
    cases he
    rfl
  refine ⟨hc.1,?_,distinct,growRow_values lo qs sign distinct s m (fun w hw => ready.2 w (List.mem_toFinset.mpr hw))⟩
  intro w hw hout
  rw [(growRow_frame sign qs s m).2 w (by
    intro hq
    exact hout (by rw [hlive]; exact Finset.mem_union_right _ (List.mem_toFinset.mpr hq)))]
  exact ready.1 w hw hout

end ECDSAAdd.Arithmetic.Paper935
