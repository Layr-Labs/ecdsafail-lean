import ECDSAAdd.Arithmetic.Paper935.PublicSlotTotal

namespace ECDSAAdd.Arithmetic.Paper935

/-- Width and ownership are properties of the compiled layout alone. The
existing resize correctness theorem can be specialized to the all-zero state,
which satisfies every numeric width, to extract these static conclusions. -/
theorem planRowResize_layout (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (h : planRowResize A r width=some (B,out,p)) :
    out.payload.length=width ∧ out.wires.Nodup ∧ out.wires.toFinset⊆B.live := by
  let s : State := ⟨false,fun _ => false⟩
  have zero : r.value s.basis=0 := by
    unfold WindowRow.value WindowRow.wires
    rw [signedRegValue_msb]
    have hz := (regValue_zero (r.payload++[r.sign]) s.basis).mpr (fun _ _ => rfl)
    simp [hz,s]
  have fits : PayloadFits width (r.value s.basis) := by
    rw [zero]
    have positive : 0<(2^width:Nat) := Nat.pow_pos (by decide)
    unfold PayloadFits
    constructor <;> omega
  have result := planRowResize_correct A B r out width p h s [] (fun _ _ _ => rfl) fits
  refine ⟨result.1,?_,?_⟩
  · have nd := List.nodup_cons.mp result.2.1
    apply List.nodup_append'.mpr
    exact ⟨nd.2,by simp,List.disjoint_left.mpr
      (fun q hq hs => nd.1 ((List.mem_singleton.mp hs) ▸ hq))⟩
  · simpa only [WindowRow.wires,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
      Finset.union_singleton,Finset.insert_empty] using result.2.2.1

/-- A successful physical resize preserves any separated owned register list,
including metadata and the rows not currently being resized. -/
theorem planRowResize_frame_layout (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (h : planRowResize A r width=some (B,out,p)) (fixed : List Wire)
    (distinct : (fixed++r.wires).Nodup) (owned : (fixed++r.wires).toFinset⊆A.live) :
    (fixed++out.wires).Nodup ∧ (fixed++out.wires).toFinset⊆B.live := by
  have parts := List.nodup_append'.mp distinct
  have layout := planRowResize_layout A B r out width p h
  have fixedOwned (q : Wire) (hq : q∈fixed) : q∈A.live :=
    owned (List.mem_toFinset.mpr (List.mem_append_left _ hq))
  have fixedKeep (q : Wire) (hq : q∈fixed) : q∈B.live :=
    (planRowResize_locality A B r out width p h ⟨false,fun _ => false⟩ [] q (fixedOwned q hq)
      (fun hr => List.disjoint_left.mp parts.2.2 hq hr)).1
  constructor
  · apply List.nodup_append'.mpr
    refine ⟨parts.1,layout.2.1,List.disjoint_left.mpr ?_⟩
    intro q hq ho
    have old := planRowResize_old_sites A B r out width p h q ho (fixedOwned q hq)
    exact List.disjoint_left.mp parts.2.2 hq old
  · intro q hq
    rcases List.mem_append.mp (List.mem_toFinset.mp hq) with hf|ho
    · exact fixedKeep q hf
    · exact layout.2.2 (List.mem_toFinset.mpr ho)

end ECDSAAdd.Arithmetic.Paper935
