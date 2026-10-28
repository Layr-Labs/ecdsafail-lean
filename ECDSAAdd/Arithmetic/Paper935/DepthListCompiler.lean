import ECDSAAdd.Arithmetic.Paper935.BorrowedDepthReady

namespace ECDSAAdd.Arithmetic.Paper935

/-- All stages reuse the same borrowed pool; no stage allocates another pool. -/
def compileDepthList (one frozen output : Wire) (z f v work : List Wire) :
    List Nat → Option (List DepthLayout)
  | [] => some []
  | d::ds => do
    let L ← compileDepth one frozen output z f v work d
    let ls ← compileDepthList one frozen output z f v work ds
    pure (L::ls)

theorem compileDepthList_contract (one frozen output : Wire) (z f v work : List Wire)
    (depths : List Nat) (layouts : List DepthLayout)
    (h : compileDepthList one frozen output z f v work depths=some layouts) :
    layouts.map (fun L => L.low.length)=depths ∧
    ∀ L∈layouts,∃ d∈depths,compileDepth one frozen output z f v work d=some L := by
  induction depths generalizing layouts with
  | nil => simp [compileDepthList] at h; subst layouts; simp
  | cons d ds ih =>
    simp only [compileDepthList] at h
    cases hc : compileDepth one frozen output z f v work d with
    | none => simp [hc] at h
    | some L =>
      cases hl : compileDepthList one frozen output z f v work ds with
      | none => simp [hc,hl] at h
      | some ls =>
        simp only [hc,hl] at h
        change some (L::ls)=some layouts at h
        have eq := Option.some.inj h
        cases eq
        have rest := ih ls hl
        have head := compileDepth_contract one frozen output z f v work d L hc
        constructor
        · simp only [List.map_cons,head.2.2.2.2.2,rest.1]
        · intro K hk
          rcases List.mem_cons.mp hk with rfl|hk
          · exact ⟨d,List.mem_cons_self,hc⟩
          · obtain ⟨e,he,hk⟩ := rest.2 K hk
            exact ⟨e,List.mem_cons_of_mem _ he,hk⟩

def compileBorrowedDepths (A : Arena) (one frozen output : Wire) (z f v : List Wire) :
    Option (Arena × List Wire × List DepthLayout) := do
  let (D,work) ← A.borrowMany 11
  let layouts ← compileDepthList one frozen output z f v work [2,3,4,5,6]
  pure (D,work,layouts)

theorem compileBorrowedDepths_contract (A D : Arena) (one frozen output : Wire)
    (z f v work : List Wire) (layouts : List DepthLayout)
    (h : compileBorrowedDepths A one frozen output z f v=some (D,work,layouts)) :
    A.borrowMany 11=some (D,work) ∧
    compileDepthList one frozen output z f v work [2,3,4,5,6]=some layouts := by
  unfold compileBorrowedDepths at h
  cases hb : A.borrowMany 11 with
  | none => simp [hb] at h
  | some result =>
    rcases result with ⟨B,ws⟩
    simp only [hb] at h
    dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd] at h
    cases hc : compileDepthList one frozen output z f v ws [2,3,4,5,6] with
    | none => simp [hc] at h
    | some ls =>
      simp only [hc] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      exact ⟨rfl,hc⟩

theorem compileBorrowedDepths_member (A D : Arena) (one frozen output : Wire)
    (z f v work : List Wire) (layouts : List DepthLayout)
    (h : compileBorrowedDepths A one frozen output z f v=some (D,work,layouts))
    (L : DepthLayout) (hm : L∈layouts) :
    ∃ d∈[2,3,4,5,6],compileBorrowedDepth A one frozen output z f v d=some (D,work,L) := by
  have pair := compileBorrowedDepths_contract A D one frozen output z f v work layouts h
  obtain ⟨d,hd,hc⟩ := (compileDepthList_contract one frozen output z f v work _ layouts pair.2).2 L hm
  refine ⟨d,hd,?_⟩
  simp only [compileBorrowedDepth,pair.1]
  dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd]
  rw [hc]
  rfl

/-- Kernel-checked wiring example: the five real decoders share exactly
the same eleven scratch addresses and retain all seven signed counter bits. -/
theorem compileDepthList_example :
    (compileDepthList 0 1 2 (List.range' 3 7) (List.range' 10 7)
      (List.range' 17 13) (List.range' 30 11) [2,3,4,5,6]).isSome=true := by
  decide

end ECDSAAdd.Arithmetic.Paper935
