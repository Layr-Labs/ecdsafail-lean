import ECDSAAdd.Arithmetic.Paper935.Arena

namespace ECDSAAdd.Arithmetic.Paper935

/-- Deterministically select the least free physical address in an allowed
band. This is a public compiler allocation choice, not a quantum test. -/
def Arena.borrowFrom (A : Arena) (pool : Finset Wire) : Option (Arena × Wire) :=
  if hp : pool⊆arenaWires then
    if h : (pool\A.live).Nonempty then
      let q := (pool\A.live).min' h
      some (⟨insert q A.live,by
        intro r hr
        rcases Finset.mem_insert.mp hr with hr | hr
        · subst r; exact hp (Finset.mem_sdiff.mp (Finset.min'_mem _ h)).1
        · exact A.bounded hr⟩,q)
    else none
  else none

theorem Arena.borrowFrom_success (A : Arena) (pool : Finset Wire) :
    (∃ B q,A.borrowFrom pool=some (B,q)) ↔ pool⊆arenaWires ∧ (pool\A.live).Nonempty := by
  unfold borrowFrom
  split
  · split <;> simp_all
  · simp_all

theorem Arena.borrowFrom_contract (A B : Arena) (pool : Finset Wire) (q : Wire)
    (h : A.borrowFrom pool=some (B,q)) :
    q∈pool ∧ q∉A.live ∧ A.reserve {q}=some B := by
  unfold borrowFrom at h
  split at h
  next hp =>
    split at h
    next hn =>
      cases h
      have hq := Finset.mem_sdiff.mp (Finset.min'_mem (pool\A.live) hn)
      refine ⟨hq.1,hq.2,?_⟩
      have hs : {(pool\A.live).min' hn}⊆arenaWires := by
        simpa using hp hq.1
      have hd : Disjoint A.live {(pool\A.live).min' hn} := by
        simpa using hq.2
      simp [Arena.reserve,hs,hd]
    next hn => simp at h
  next hp => simp at h

theorem Arena.borrowFrom_ready (A B : Arena) (pool : Finset Wire) (q : Wire)
    (s : BasisState) (hr : A.Ready s) (h : A.borrowFrom pool=some (B,q)) :
    B.Ready s ∧ s q=false := by
  have hb := A.reserve_ready B {q} s hr (A.borrowFrom_contract B pool q h).2.2
  exact ⟨hb.1,hb.2 q (by simp)⟩

/-- Try home bands in public priority order, stopping at the first usable
one. Invalid or exhausted bands do not create external scratch. -/
def Arena.borrowFirst (A : Arena) : List (Finset Wire) → Option (Arena × Wire)
  | [] => none
  | pool::pools => match A.borrowFrom pool with
    | some result => some result
    | none => A.borrowFirst pools

theorem Arena.borrowFirst_contract (A B : Arena) (pools : List (Finset Wire)) (q : Wire)
    (h : A.borrowFirst pools=some (B,q)) :
    ∃ pool∈pools,A.borrowFrom pool=some (B,q) := by
  induction pools with
  | nil => simp [borrowFirst] at h
  | cons pool pools ih =>
    simp only [borrowFirst] at h
    split at h
    next result he =>
      cases h
      exact ⟨pool,by simp,he⟩
    next he =>
      obtain ⟨p,hp,hb⟩ := ih h
      exact ⟨p,List.mem_cons_of_mem _ hp,hb⟩

theorem Arena.borrowFirst_none (A : Arena) (pools : List (Finset Wire)) :
    A.borrowFirst pools=none ↔ ∀ pool∈pools,A.borrowFrom pool=none := by
  induction pools with
  | nil => simp [borrowFirst]
  | cons pool pools ih =>
    cases h : A.borrowFrom pool <;> simp [borrowFirst,h,ih]

theorem Arena.borrowFirst_ready (A B : Arena) (pools : List (Finset Wire)) (q : Wire)
    (s : BasisState) (hr : A.Ready s) (h : A.borrowFirst pools=some (B,q)) :
    B.Ready s ∧ s q=false ∧ A.reserve {q}=some B := by
  obtain ⟨pool,_,hp⟩ := A.borrowFirst_contract B pools q h
  have hb := A.borrowFrom_ready B pool q s hr hp
  exact ⟨hb.1,hb.2,(A.borrowFrom_contract B pool q hp).2.2⟩

/-- With the whole physical arena as fallback, a borrow succeeds exactly
when one quantum site remains available. -/
theorem Arena.borrow_capacity (A : Arena) :
    (∃ B q,A.borrowFrom arenaWires=some (B,q)) ↔ A.live.card<935 := by
  rw [A.borrowFrom_success]
  simp only [subset_refl,true_and]
  constructor
  · intro h
    have hn := Finset.sdiff_nonempty.mp h
    have hs : A.live ⊂ arenaWires := ⟨A.bounded,hn⟩
    simpa [arenaWires] using Finset.card_lt_card hs
  · intro h
    apply Finset.sdiff_nonempty_of_card_lt_card
    simpa [arenaWires] using h

theorem Arena.borrowFirst_fallback (A : Arena) (pools : List (Finset Wire))
    (hp : arenaWires∈pools) (hc : A.live.card<935) :
    ∃ B q,A.borrowFirst pools=some (B,q) := by
  cases h : A.borrowFirst pools with
  | none =>
    have hf := (A.borrowFirst_none pools).mp h arenaWires hp
    obtain ⟨B,q,hb⟩ := A.borrow_capacity.mpr hc
    rw [hf] at hb
    have hh := congrArg Option.isSome hb
    change false=true at hh
    cases hh
  | some r => exact ⟨r.1,r.2,rfl⟩

end ECDSAAdd.Arithmetic.Paper935
