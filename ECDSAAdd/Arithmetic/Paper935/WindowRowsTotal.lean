import ECDSAAdd.Arithmetic.Paper935.RowResizeTotal

namespace ECDSAAdd.Arithmetic.Paper935

private theorem swap_nodup (a b c : List Wire) (h : (a++b++c).Nodup) : (a++c++b).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hc := List.nodup_iff_count.mp h q
  simp only [List.count_append] at hc ⊢
  omega

private theorem swap_owned (A : Arena) (a b c : List Wire) (h : (a++b++c).toFinset⊆A.live) :
    (a++c++b).toFinset⊆A.live := by
  simpa only [List.toFinset_append,Finset.union_assoc,Finset.union_comm,Finset.union_left_comm] using h

/-- A conservative allocation bound for the actual ordered row transitions:
shrinking can only improve this sum of positive growth requests. -/
def rowGrowth : List (WindowRow × Nat) → Nat
  | [] => 0
  | (r,w)::rest => (w-r.payload.length)+rowGrowth rest

/-- The actual row-bank planner succeeds under one static ownership invariant
and a bound on total positive growth. Registers outside the resized bank remain
owned and disjoint from its returned rows. -/
theorem planWindowRows_exists (requests : List (WindowRow × Nat)) (A : Arena) (fixed : List Wire)
    (distinct : (fixed++(requests.map Prod.fst).flatMap WindowRow.wires).Nodup)
    (owned : (fixed++(requests.map Prod.fst).flatMap WindowRow.wires).toFinset⊆A.live)
    (budget : A.live.card+rowGrowth requests≤935) :
    ∃ C outs p,planWindowRows A requests=some (C,outs,p) ∧
      (fixed++outs.flatMap WindowRow.wires).Nodup ∧
      (fixed++outs.flatMap WindowRow.wires).toFinset⊆C.live ∧
      C.live.card≤A.live.card+rowGrowth requests := by
  induction requests generalizing A fixed with
  | nil => exact ⟨A,[],[],rfl,distinct,owned,by simp [rowGrowth]⟩
  | cons request rest ih =>
    rcases request with ⟨row,width⟩
    let tail := (rest.map Prod.fst).flatMap WindowRow.wires
    change (fixed++(row.wires++tail)).Nodup at distinct
    change (fixed++(row.wires++tail)).toFinset⊆A.live at owned
    have rowsDistinct := (List.nodup_append'.mp distinct).2.1
    have rowDistinct := (List.nodup_append'.mp rowsDistinct).1
    have rowOwned : row.wires.toFinset⊆A.live := by
      intro q hq
      exact owned (List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_append_left _ (List.mem_toFinset.mp hq))))
    have signDistinct : (row.sign::row.payload).Nodup := by
      have := (List.nodup_append'.mp rowDistinct)
      exact List.nodup_cons.mpr ⟨fun hs => List.disjoint_left.mp this.2.2 hs (by simp),this.1⟩
    have signOwned : (row.sign::row.payload).toFinset⊆A.live := by
      simpa only [WindowRow.wires,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
        Finset.union_singleton,Finset.insert_empty] using rowOwned
    obtain ⟨B,out,p,first⟩ := planRowResize_exists A row width signDistinct signOwned (by
      simp only [rowGrowth] at budget
      omega)
    have firstCard := planRowResize_live_bound A B row out width p first
    have firstFrame := planRowResize_frame_layout A B row out width p first (fixed++tail)
      (swap_nodup fixed row.wires tail (by simpa only [List.append_assoc] using distinct))
      (swap_owned A fixed row.wires tail (by simpa only [List.append_assoc] using owned))
    have nextDistinct : ((fixed++out.wires)++tail).Nodup := swap_nodup fixed tail out.wires firstFrame.1
    have nextOwned : ((fixed++out.wires)++tail).toFinset⊆B.live := swap_owned B fixed tail out.wires firstFrame.2
    obtain ⟨C,outs,q,remaining,finalDistinct,finalOwned,finalCard⟩ := ih B (fixed++out.wires) nextDistinct nextOwned (by
      simp only [rowGrowth] at budget
      omega)
    have inputCheck : rowsOwned A (row::rest.map Prod.fst) := by
      refine ⟨rowsDistinct,?_⟩
      intro w hw
      exact owned (List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp hw)))
    have outputCheck : rowsOwned C (out::outs) := by
      refine ⟨?_,?_⟩
      · exact (List.nodup_append'.mp (show (fixed++(out.wires++outs.flatMap WindowRow.wires)).Nodup from
          by simpa only [List.append_assoc] using finalDistinct)).2.1
      · intro w hw
        apply finalOwned
        simpa only [List.mem_toFinset,List.flatMap_cons,List.mem_append,or_assoc] using
          (Or.inr (List.mem_toFinset.mp hw) : w∈fixed ∨ w∈(out::outs).flatMap WindowRow.wires)
    refine ⟨C,out::outs,p++q,?_,?_,?_,?_⟩
    · rw [planWindowRows,if_pos inputCheck,first]
      dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd]
      rw [remaining]
      dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd]
      rw [if_pos outputCheck]
      rfl
    · simpa only [List.flatMap_cons,List.append_assoc] using finalDistinct
    · simpa only [List.flatMap_cons,List.append_assoc] using finalOwned
    · simp only [rowGrowth]
      omega

/-- Actual returned payload widths are determined by the public requests,
independently of the represented input state. -/
theorem planWindowRows_widths (requests : List (WindowRow × Nat)) (A C : Arena)
    (outs : List WindowRow) (p : Program)
    (h : planWindowRows A requests=some (C,outs,p)) :
    outs.map (fun r => r.payload.length)=requests.map Prod.snd := by
  induction requests generalizing A C outs p with
  | nil => cases h; rfl
  | cons request rest ih =>
    rcases request with ⟨row,width⟩
    rw [planWindowRows] at h
    split at h
    next inputCheck =>
      obtain ⟨⟨B,out,pf⟩,first,h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨D,tail,q⟩,remaining,h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      next outputCheck =>
        cases h
        simp only [List.map_cons]
        rw [(planRowResize_layout A B row out width pf first).1,ih B C tail q remaining]
      next invalid => simp at h
    next invalid => simp at h

end ECDSAAdd.Arithmetic.Paper935
