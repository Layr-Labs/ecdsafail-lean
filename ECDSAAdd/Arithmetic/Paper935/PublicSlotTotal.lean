import ECDSAAdd.Arithmetic.Paper935.PostCompilerTotal

namespace ECDSAAdd.Arithmetic.Paper935

/-- The full allocated post-stage port set, not only the gates used in one
execution, is contained in its actual arena. -/
theorem compileBorrowedPost_ports (A D : Arena) (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat) (P : WindowPostLayout)
    (h : compileBorrowedPost A armed one zf frozen fire active inputs record width offset=some (D,work,P))
    (owned : ([one,zf,frozen,fire,active]++inputs++record).toFinset⊆A.live) :
    P.ports.toFinset⊆D.live := by
  have pair := compileBorrowedPost_contract A D armed one zf frozen fire active inputs record work width offset P h
  have live := (A.borrowMany_live D _ work pair.1).1
  apply (compilePost_ports armed one zf frozen fire active inputs record work width offset P pair.2).trans
  rw [live]
  have all := Finset.union_subset_union owned (Finset.Subset.refl work.toFinset)
  simpa only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.insert_union,
    Finset.empty_union,Finset.union_assoc] using all

/-- The unarmed public slot needs no probe width, offset capacity or extra
allocation premise. Its fixed retirement gates are checked directly. -/
theorem compileCheckedPublicSlot_unarmed_exists (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (probeWidth offset : Nat) (front : SlotFront)
    (compiled : compileSlotFront A b addWidth exitWidth F=some front)
    (physical : front.PhysicalChecks F) (frozenActive : F.frozen≠F.active) (workActive : F.work1≠F.active)
    (owned : [F.frozen,F.work1,F.active].toFinset⊆arenaWires) :
    ∃ P,compileCheckedPublicSlot A b addWidth exitWidth F false probeWidth offset=some P ∧ P.front=front := by
  let P : PublicSlot := ⟨front,none,front.exitArena,[]⟩
  have publicCompiled : compilePublicSlot A b addWidth exitWidth F false probeWidth offset=some P := by
    simp [compilePublicSlot,compiled,P]
  have post : P.PostChecks F := ⟨frozenActive,workActive,owned⟩
  refine ⟨P,?_,rfl⟩
  rw [compileCheckedPublicSlot,publicCompiled]
  dsimp only [Bind.bind,Option.bind]
  rw [if_pos ⟨physical,post⟩]

/-- Once the arithmetic front exists and passes its static checks, the actual
armed public slot succeeds from separated owned post inputs and pool capacity. -/
theorem compileCheckedPublicSlot_armed_exists (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (probeWidth offset : Nat) (front : SlotFront)
    (compiled : compileSlotFront A b addWidth exitWidth F=some front)
    (physical : front.PhysicalChecks F) (positive : 0<probeWidth)
    (distinct : ([F.one,F.work0,F.frozen,F.work1,F.active]++front.exitBank.g.wires++F.offset).Nodup)
    (owned : ([F.one,F.work0,F.frozen,F.work1,F.active]++front.exitBank.g.wires++F.offset).toFinset⊆front.exitArena.live)
    (budget : front.exitArena.live.card+postPoolSize front.exitBank.g.wires F.offset probeWidth≤935)
    (offsetFits : offset<2^F.offset.length) :
    ∃ P,compileCheckedPublicSlot A b addWidth exitWidth F true probeWidth offset=some P ∧ P.front=front := by
  obtain ⟨D,work,post,postCompiled⟩ := compileBorrowedPost_exists front.exitArena true F.one F.work0 F.frozen F.work1 F.active
    front.exitBank.g.wires F.offset probeWidth offset positive distinct owned budget (fun _ => offsetFits)
  have ports := compileBorrowedPost_ports front.exitArena D true F.one F.work0 F.frozen F.work1 F.active
    front.exitBank.g.wires F.offset work probeWidth offset post postCompiled owned
  let P : PublicSlot := ⟨front,some post,D,work⟩
  have publicCompiled : compilePublicSlot A b addWidth exitWidth F true probeWidth offset=some P := by
    simp [compilePublicSlot,compiled,postCompiled,P]
  have postChecks : P.PostChecks F := ports.trans D.bounded
  refine ⟨P,?_,rfl⟩
  rw [compileCheckedPublicSlot,publicCompiled]
  dsimp only [Bind.bind,Option.bind]
  rw [if_pos ⟨physical,postChecks⟩]

end ECDSAAdd.Arithmetic.Paper935
