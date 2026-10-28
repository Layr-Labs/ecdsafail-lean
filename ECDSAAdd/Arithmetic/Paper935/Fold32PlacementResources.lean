import ECDSAAdd.Arithmetic.Paper935.Fold32Placement

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic RecordedQuantum

def fold32Footprint (f : Wire → Wire) : Finset Wire := (Finset.range 291).image f

attribute [local irreducible] fold32Reduce fold32Unreduce

private theorem rename_bound (f : Wire → Wire) (p : Program)
    (h : wires p⊆Finset.range 291) : wires (renameProgram f p)⊆fold32Footprint f := by
  rw [renameProgram_support,fold32Footprint]
  exact Finset.image_mono f h

theorem fold32Placed_support_image (f : Wire → Wire) :
    wires (fold32PlacedReduce f)=(wires fold32Reduce).image f ∧
    wires (fold32PlacedUnreduce f)=(wires fold32Unreduce).image f :=
  ⟨renameProgram_support f fold32Reduce,renameProgram_support f fold32Unreduce⟩

theorem fold32Placed_support (f : Wire → Wire) :
    wires (fold32PlacedReduce f)⊆fold32Footprint f ∧
    wires (fold32PlacedUnreduce f)⊆fold32Footprint f :=
  ⟨rename_bound f fold32Reduce fold32Reduce_support,rename_bound f fold32Unreduce fold32Unreduce_support⟩

/-- This is the cardinality of the declared layout, not of simultaneously
live ancillas in an enclosing program. -/
theorem fold32Footprint_card (f : Wire → Wire) (hf : Function.Injective f) :
    (fold32Footprint f).card=291 := by
  rw [fold32Footprint,Finset.card_image_of_injective _ hf,Finset.card_range]

private theorem physical_rename (f : Wire → Wire) (hf : Function.Injective f)
    (p : Program) (hp : GatePhysical p) : GatePhysical (renameProgram f p) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have h := hp j hj
  cases j <;> simp_all [renameInstr,PhysicalInstr,ProperGate,hf.eq_iff]

theorem fold32Placed_physical (f : Wire → Wire) (hf : Function.Injective f) :
    GatePhysical (fold32PlacedReduce f) ∧ GatePhysical (fold32PlacedUnreduce f) :=
  ⟨physical_rename f hf _ fold32Reduce_physical,physical_rename f hf _ fold32Unreduce_physical⟩

private theorem outside_frame (p : Program) (f : Wire → Wire) (h : wires p⊆fold32Footprint f)
    (s : State) (m : List Bool) (q : Wire) (hq : q∉fold32Footprint f) :
    (run p m s).basis q=s.basis q :=
  run_preserves_outside p m s q (fun mem => hq (h mem))

/-- The full ambient state returns, including wires outside the image of f.
No surjectivity assumption or equality only on selected registers is used. -/
theorem fold32Placed_roundtrip (f : Wire → Wire) (hf : Function.Injective f)
    (s : State) (m n : List Bool) (ready : Fold32PlacedReady f s.basis)
    (enabled : s.basis (f 0)=true) (flag : s.basis (f 290)=false)
    (bound : regValue (fold32Word.map f) s.basis<2*fold32Prime) :
    run (fold32PlacedUnreduce f) n (run (fold32PlacedReduce f) m s)=s := by
  have pulled := fold32Placed_roundtrip_pull f hf s m n ready enabled flag bound
  apply State.extensionality
  · simpa only [pullState] using congrArg State.phase pulled
  · funext q
    by_cases inside : q∈fold32Footprint f
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp inside
      exact congrArg (fun t : State => t.basis j) pulled
    · exact (outside_frame _ f (fold32Placed_support f).2 _ n q inside).trans
        (outside_frame _ f (fold32Placed_support f).1 s m q inside)

/-- If a caller proves its declared hosts lie in an arena, both actual
programs are supported there. No allocation success is inferred. -/
theorem fold32Placed_in_arena (f : Wire → Wire) (arena : Finset Wire)
    (hosts : fold32Footprint f⊆arena) :
    wires (fold32PlacedReduce f)∪wires (fold32PlacedUnreduce f)⊆arena :=
  Finset.union_subset (Finset.Subset.trans (fold32Placed_support f).1 hosts)
    (Finset.Subset.trans (fold32Placed_support f).2 hosts)

theorem fold32Placed_counts (f : Wire → Wire) :
    (toffoliCount (fold32PlacedReduce f)=toffoliCount fold32Reduce ∧
      measurementCount (fold32PlacedReduce f)=measurementCount fold32Reduce) ∧
    (toffoliCount (fold32PlacedUnreduce f)=toffoliCount fold32Unreduce ∧
      measurementCount (fold32PlacedUnreduce f)=measurementCount fold32Unreduce) :=
  ⟨renameProgram_counts f fold32Reduce,renameProgram_counts f fold32Unreduce⟩

end ECDSAAdd.Arithmetic.Paper935
