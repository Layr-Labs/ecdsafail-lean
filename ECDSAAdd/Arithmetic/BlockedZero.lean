import ECDSAAdd.Arithmetic.PointFixedPrimitivesPhysical

namespace ECDSAAdd.Arithmetic.BlockedZero
open RecordedQuantum

/-- A block has one persistent conjunction flag; its per-bit scratch can be
reused by every other block. -/
structure Block where
  flag : Wire
  bits : List ZeroBit

def Block.ports (b : Block) : List Wire := b.flag :: b.bits.flatMap ZeroBit.wires

def ports (bs : List Block) : List Wire := bs.flatMap Block.ports

def test (bs : List Block) (s : BasisState) : Bool :=
  bs.all (fun b => b.bits.all (fun x => !s x.input))

def clean (bs : List Block) (s : BasisState) : Prop :=
  ∀ b ∈ bs, s b.flag = false ∧ ∀ x ∈ b.bits, s x.work = false

/-- Local disjointness permits scratch reuse between different blocks. -/
def Valid (c target : Wire) : List Block → Prop
  | [] => c ≠ target
  | b::bs => (c::b.flag::b.bits.flatMap ZeroBit.wires).Nodup ∧
      target ∉ c::b.ports ∧ b.flag ∉ ports bs ∧ Valid b.flag target bs

def program (c target : Wire) : List Block → Program
  | [] => [.CX c target]
  | b::bs => zeroControlled c b.flag b.bits ++
      (program b.flag target bs ++ zeroControlled c b.flag b.bits)

private theorem input_mem {b : Block} {x : ZeroBit} (hx : x ∈ b.bits) :
    x.input ∈ b.ports := by
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨x,hx,by simp [ZeroBit.wires]⟩)

private theorem work_mem {b : Block} {x : ZeroBit} (hx : x ∈ b.bits) :
    x.work ∈ b.ports := by
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨x,hx,by simp [ZeroBit.wires]⟩)

private theorem block_mem {b : Block} {bs : List Block} (hb : b ∈ bs)
    {q : Wire} (hq : q ∈ b.ports) : q ∈ ports bs :=
  List.mem_flatMap.mpr ⟨b,hb,hq⟩

private theorem all_congr_mem {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = q x) : xs.all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons,h x (by simp),ih (fun y hy => h y (by simp [hy]))]

/-- Every tape produces the same complete state, including phase and all scratch. -/
theorem run_eq (c target : Wire) (bs : List Block) (hv : Valid c target bs)
    (s : State) (m : List Bool) (hz : clean bs s.basis) :
    run (program c target bs) m s =
      ⟨s.phase,writeBit s.basis target (s.basis target ^^ (s.basis c && test bs s.basis))⟩ := by
  induction bs generalizing c s m with
  | nil => simp [program,run,test]
  | cons b bs ih =>
    obtain ⟨hn,ht,hf,hv⟩ := hv
    have hclean := hz b (by simp)
    have hfne : b.flag ≠ target := fun h => ht (by simp [h,Block.ports])
    have hcne : c ≠ target := fun h => ht (by simp [h])
    have hcf : c ≠ b.flag := by
      exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have keepTarget (q : Wire) (hq : q ∈ b.ports) : q ≠ target :=
      fun h => ht (List.mem_cons_of_mem _ (h ▸ hq))
    have keepFlag (q : Wire) (hq : q ∈ ports bs) : q ≠ b.flag :=
      fun h => hf (h ▸ hq)
    let z := s.basis c && b.bits.all (fun x => !s.basis x.input)
    let t : State := ⟨s.phase,writeBit s.basis b.flag z⟩
    have hfirst : run (zeroControlled c b.flag b.bits) m s = t := by
      simpa [t,z,hclean.1] using zeroControlled_correct c b.flag b.bits hn s m hclean.2
    have htz : clean bs t.basis := by
      intro d hd
      have h := hz d (by simp [hd])
      constructor
      · simpa [t,writeBit,keepFlag d.flag (block_mem hd (by simp [Block.ports]))] using h.1
      · intro x hx
        simpa [t,writeBit,keepFlag x.work (block_mem hd (work_mem hx))] using h.2 x hx
    have htest : test bs t.basis = test bs s.basis := by
      unfold test
      apply all_congr_mem
      intro d hd
      apply all_congr_mem
      intro x hx
      simp [t,writeBit,keepFlag x.input (block_mem hd (input_mem hx))]
    let v : State := ⟨s.phase,writeBit t.basis target
      (t.basis target ^^ (t.basis b.flag && test bs t.basis))⟩
    have hlast (tape : List Bool) : run (zeroControlled c b.flag b.bits) tape v =
        ⟨s.phase,writeBit v.basis b.flag false⟩ := by
      have hwork : ∀ x ∈ b.bits, v.basis x.work = false := by
        intro x hx
        have hxf : x.work ≠ b.flag := by
          intro he
          exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
            (List.mem_flatMap.mpr ⟨x,hx,by simp [ZeroBit.wires,he]⟩)
        simpa [v,t,writeBit,keepTarget x.work (work_mem hx),hxf] using hclean.2 x hx
      rw [zeroControlled_correct c b.flag b.bits hn v tape hwork]
      have hall : b.bits.all (fun x => !v.basis x.input) =
          b.bits.all (fun x => !s.basis x.input) := by
        apply all_congr_mem
        intro x hx
        have hxf : x.input ≠ b.flag := by
          intro he
          exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
            (List.mem_flatMap.mpr ⟨x,hx,by simp [ZeroBit.wires,he]⟩)
        simp [v,t,writeBit,keepTarget x.input (input_mem hx),hxf]
      rw [hall]
      simp [v,t,writeBit,hfne,hcne,hcf,z]
    rw [program,run_append,run_take,hfirst,run_append,run_take]
    rw [ih b.flag hv t _ htz]
    change run (zeroControlled c b.flag b.bits) _ v = _
    rw [hlast]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q=target
    · subst q
      dsimp only [v]
      rw [htest]
      simp [t,writeBit,hfne.symm,test,z,Bool.and_assoc]
    · by_cases hqf : q=b.flag
      · subst q; simp [writeBit,hq,hclean.1]
      · simp [v,t,writeBit,hq,hqf]

def inputs (bs : List Block) : List Wire := bs.flatMap (fun b => b.bits.map ZeroBit.input)

theorem test_eq_zero (bs : List Block) (s : BasisState) :
    test bs s = decide (regValue (inputs bs) s = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [test,inputs,List.all_eq_true,decide_eq_true_eq,regValue_zero,
    List.mem_flatMap,List.mem_map,forall_exists_index,and_imp]
  constructor
  · intro h w b hb x hx he
    subst w
    simpa using h b hb x hx
  · intro h b hb x hx
    simpa using h x.input b hb x hx rfl

theorem counts (c target : Wire) (bs : List Block) :
    toffoliCount (program c target bs) = 2 * (inputs bs).length ∧
    measurementCount (program c target bs) = 2 * (inputs bs).length := by
  induction bs generalizing c with
  | nil => simp [program,inputs,toffoliCount,measurementCount]
  | cons b bs ih =>
    have h := zeroControlled_counts c b.flag b.bits
    simp only [program,toffoliCount_append,measurementCount_append,h.1,h.2,
      (ih b.flag).1,(ih b.flag).2,inputs,List.flatMap_cons,List.length_append,List.length_map]
    constructor <;> omega

theorem support (c target : Wire) (bs : List Block) :
    wires (program c target bs) ⊆ (c::target::ports bs).toFinset := by
  induction bs generalizing c with
  | nil => simp [program,ports,wires,Instr.wires]
  | cons b bs ih =>
    rw [program,wires_append,wires_append]
    have hlocal : wires (zeroControlled c b.flag b.bits) ⊆
        (c::target::ports (b::bs)).toFinset := by
      rw [zeroControlled_wires]
      intro q hq
      simp only [List.mem_toFinset,List.mem_cons,ports,List.flatMap_cons,Block.ports,
        List.mem_append] at hq ⊢
      tauto
    refine Finset.union_subset hlocal (Finset.union_subset ?_ hlocal)
    apply (ih b.flag).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,ports,List.flatMap_cons,Block.ports,
      List.mem_append] at hq ⊢
    tauto

/-- Physical validity follows from each local gate layout, despite scratch reuse. -/
theorem physical (c target : Wire) (bs : List Block) (hv : Valid c target bs) :
    GatePhysical (program c target bs) := by
  induction bs generalizing c with
  | nil => simpa [program,GatePhysical,PhysicalInstr,ProperGate] using hv
  | cons b bs ih =>
    obtain ⟨hn,_,_,hv⟩ := hv
    simp only [program,gatePhysical_append]
    exact ⟨zeroControlled_physical c b.flag b.bits hn,
      ih b.flag hv,zeroControlled_physical c b.flag b.bits hn⟩

/-- All per-bit scratch comes from one common pool, not one pool per block. -/
theorem shared_support (c target : Wire) (bs : List Block) (scratch : List Wire)
    (hw : ∀ b ∈ bs, ∀ x ∈ b.bits, x.work ∈ scratch) :
    wires (program c target bs) ⊆
      (c::target::(inputs bs ++ bs.map Block.flag ++ scratch)).toFinset := by
  apply (support c target bs).trans
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
  rcases hq with hq | hq | hq
  · exact Or.inl hq
  · exact Or.inr (Or.inl hq)
  · apply Or.inr ∘ Or.inr
    obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    simp only [Block.ports,List.mem_cons] at hq
    rcases hq with hq | hq
    · subst q
      simp only [List.mem_append,List.mem_map]
      exact Or.inl (Or.inr ⟨b,hb,rfl⟩)
    · obtain ⟨x,hx,hq⟩ := List.mem_flatMap.mp hq
      simp only [ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq | hq
      · subst q
        apply List.mem_append_left
        apply List.mem_append_left
        exact List.mem_flatMap.mpr ⟨b,hb,List.mem_map.mpr ⟨x,hx,rfl⟩⟩
      · subst q
        exact List.mem_append_right _ (hw b hb x hx)

/-- The input wires plus one flag per block, the shared scratch, control and
output suffice for the actual instruction list. -/
theorem qubits_le (c target : Wire) (bs : List Block) (scratch : List Wire)
    (hw : ∀ b ∈ bs, ∀ x ∈ b.bits, x.work ∈ scratch) :
    qubitCount (program c target bs) ≤ (inputs bs).length + bs.length + scratch.length + 2 := by
  calc
    qubitCount (program c target bs) ≤
        (c::target::(inputs bs ++ bs.map Block.flag ++ scratch)).toFinset.card :=
      Finset.card_le_card (shared_support c target bs scratch hw)
    _ ≤ (c::target::(inputs bs ++ bs.map Block.flag ++ scratch)).length := List.toFinset_card_le _
    _ = _ := by simp; omega

end ECDSAAdd.Arithmetic.BlockedZero
