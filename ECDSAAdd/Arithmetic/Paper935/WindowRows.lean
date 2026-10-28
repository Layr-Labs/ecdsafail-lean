import ECDSAAdd.Arithmetic.Paper935.WindowAllocator

namespace ECDSAAdd.Arithmetic.Paper935

def rowsOwned (A : Arena) (rows : List WindowRow) : Prop :=
  (rows.flatMap WindowRow.wires).Nodup ∧ (rows.flatMap WindowRow.wires).toFinset⊆A.live

instance (A : Arena) (rows : List WindowRow) : Decidable (rowsOwned A rows) :=
  inferInstanceAs (Decidable ((rows.flatMap WindowRow.wires).Nodup ∧ (rows.flatMap WindowRow.wires).toFinset⊆A.live))

/-- Resize a finite public row bank. Both initial and final ownership checks
are compiler checks; they do not inspect quantum data or clear dirty wires. -/
def planWindowRows (A : Arena) : List (WindowRow × Nat) → Option (Arena × List WindowRow × Program)
  | [] => some (A,[],[])
  | (row,width)::rest =>
    if rowsOwned A (row::rest.map Prod.fst) then do
      let (B,out,p) ← planRowResize A row width
      let (C,outs,q) ← planWindowRows B rest
      if rowsOwned C (out::outs) then pure (C,out::outs,p++q) else none
    else none

private theorem value_congr (r : WindowRow) (s t : BasisState)
    (h : ∀ w∈r.wires,s w=t w) : r.value s=r.value t := by
  unfold WindowRow.value signedRegValue
  rw [regValue_congr r.wires s t h]

theorem planWindowRows_resources (requests : List (WindowRow × Nat))
    (A C : Arena) (outs : List WindowRow) (p : Program)
    (h : planWindowRows A requests=some (C,outs,p)) :
    ProperProgram p ∧ toffoliCount p=0 ∧ measurementCount p=0 ∧ wires p⊆arenaWires := by
  induction requests generalizing A C outs p with
  | nil => simp only [planWindowRows,Option.some.injEq,Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl,rfl⟩; simp [ProperProgram,toffoliCount,measurementCount,wires]
  | cons request rest ih =>
    rcases request with ⟨row,width⟩
    simp only [planWindowRows] at h
    split at h
    next hv =>
      cases hf : planRowResize A row width with
      | none => simp [hf] at h
      | some first =>
        rcases first with ⟨B,out,pf⟩
        simp only [hf] at h
        dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd] at h
        cases ht : planWindowRows B rest with
        | none => simp [ht] at h
        | some tail =>
          rcases tail with ⟨D,ot,pt⟩
          simp only [ht] at h
          split at h
          next hv' =>
            cases h
            have a := planRowResize_resources A B row out width pf hf
            have b := ih B C ot pt ht
            refine ⟨?_,?_,?_,?_⟩
            · intro g hg
              exact (List.mem_append.mp hg).elim (a.1 g) (b.1 g)
            · rw [toffoliCount_append,a.2.1,b.2.1]
            · rw [measurementCount_append,a.2.2.1,b.2.2.1]
            · rw [wires_append]; exact Finset.union_subset a.2.2.2 b.2.2.2
          next hv' => simp at h
    next hv => simp at h

theorem planWindowRows_correct (requests : List (WindowRow × Nat))
    (A C : Arena) (outs : List WindowRow) (p : Program)
    (h : planWindowRows A requests=some (C,outs,p)) (s : State) (m : List Bool)
    (hready : A.Ready s.basis)
    (hfit : ∀ r∈requests,PayloadFits r.2 (r.1.value s.basis)) :
    rowsOwned C outs ∧ C.Ready (run p m s).basis ∧
    outs.map (fun r => r.value (run p m s).basis)=requests.map (fun r => r.1.value s.basis) ∧
    outs.map (fun r => r.payload.length)=requests.map Prod.snd ∧
    (∀ w∈A.live,w∉(requests.map Prod.fst).flatMap WindowRow.wires →
      w∈C.live ∧ (run p m s).basis w=s.basis w) := by
  induction requests generalizing A C outs p s m with
  | nil =>
    simp only [planWindowRows,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    simpa [rowsOwned,run] using hready
  | cons request rest ih =>
    rcases request with ⟨row,width⟩
    simp only [planWindowRows] at h
    split at h
    next hv =>
      cases hf : planRowResize A row width with
      | none => simp [hf] at h
      | some first =>
        rcases first with ⟨B,out,pf⟩
        simp only [hf] at h
        dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd] at h
        cases ht : planWindowRows B rest with
        | none => simp [ht] at h
        | some tail =>
          rcases tail with ⟨D,ot,pt⟩
          simp only [ht] at h
          split at h
          next hv' =>
            cases h
            let t := run pf m s
            have first := planRowResize_correct A B row out width pf hf s m hready (hfit (row,width) (by simp))
            have hd : ∀ a∈row.wires,∀ b∈(rest.map Prod.fst).flatMap WindowRow.wires,a≠b := by
              exact (List.nodup_append.mp hv.1).2.2
            have restOwn (w : Wire) (hw : w∈(rest.map Prod.fst).flatMap WindowRow.wires) : w∈A.live := by
              apply hv.2
              simpa only [List.mem_toFinset,List.flatMap_cons,List.mem_append] using Or.inr hw
            have restKeep (w : Wire) (hw : w∈(rest.map Prod.fst).flatMap WindowRow.wires) :
                w∈B.live ∧ t.basis w=s.basis w :=
              planRowResize_locality A B row out width pf hf s m w (restOwn w hw)
                (fun hr => hd w hr w hw rfl)
            have member (r : WindowRow × Nat) (hr : r∈rest) (w : Wire) (hw : w∈r.1.wires) :
                w∈(rest.map Prod.fst).flatMap WindowRow.wires :=
              List.mem_flatMap.mpr ⟨r.1,List.mem_map.mpr ⟨r,hr,rfl⟩,hw⟩
            have tailFits : ∀ r∈rest,PayloadFits r.2 (r.1.value t.basis) := by
              intro r hr
              rw [value_congr r.1 t.basis s.basis (fun w hw => (restKeep w (member r hr w hw)).2)]
              exact hfit r (List.mem_cons_of_mem _ hr)
            have last := ih B C ot pt ht t m first.2.2.2.1 tailFits
            have outOwn (w : Wire) (hw : w∈out.wires) : w∈B.live := by
              apply first.2.2.1
              simpa [WindowRow.wires,or_comm] using hw
            have outAway (w : Wire) (hw : w∈out.wires) : w∉(rest.map Prod.fst).flatMap WindowRow.wires := by
              intro ht
              have hold := planRowResize_old_sites A B row out width pf hf w hw (restOwn w ht)
              exact hd w hold w ht rfl
            have outValue : out.value (run pt m t).basis=out.value t.basis :=
              value_congr out _ _ (fun w hw => (last.2.2.2.2 w (outOwn w hw) (outAway w hw)).2)
            have count := (planRowResize_resources A B row out width pf hf).2.2.1
            rw [run_append,run_take,count,List.drop_zero]
            change rowsOwned C (out::ot) ∧ C.Ready (run pt m t).basis ∧ _
            refine ⟨hv',last.2.1,?_,?_,?_⟩
            · simp only [List.map_cons]
              rw [outValue,first.2.2.2.2,last.2.2.1]
              congr 1
              apply List.map_congr_left
              intro r hr
              exact value_congr r.1 t.basis s.basis (fun w hw => (restKeep w (member r hr w hw)).2)
            · simp only [List.map_cons]
              rw [first.1,last.2.2.2.1]
            · intro w hw hout
              have hnot : w∉row.wires ∧ w∉(rest.map Prod.fst).flatMap WindowRow.wires := by
                simpa only [List.map_cons,List.flatMap_cons,List.mem_append,not_or] using hout
              have a := planRowResize_locality A B row out width pf hf s m w hw hnot.1
              have b := last.2.2.2.2 w a.1 hnot.2
              exact ⟨b.1,b.2.trans a.2⟩
          next hv' => simp at h
    next hv => simp at h

end ECDSAAdd.Arithmetic.Paper935
