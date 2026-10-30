import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Arithmetic.SkywalkIntegerLoopCore
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Baselines.SlotMapped

/-! A legal nonzero first trit supplies a zero host without another site.
The first-trit premises are explicit and must come from the actual trace. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace ECDSAAdd.Entrant.G0CarryLoan5
open Arithmetic RecordedQuantum Challenge Baselines
attribute [local irreducible] run wires

def expose (j g : Wire) : Program := [.CX j g,.X g]
def restore (j g : Wire) : Program := [.X g,.CX j g]
def program (j g carry : Wire) (P : Program) : Program :=
  expose j g++renameProgram (Equiv.swap carry g) P++restore j g

private theorem pull_swap_clean (a b : Wire) (s : State)
    (ha : s.basis a=false) (hb : s.basis b=false) : pullState (Equiv.swap a b) s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (Equiv.swap a b q)=s.basis q
    by_cases qa : q=a
    · subst q; simp only [Equiv.swap_apply_left,ha,hb]
    by_cases qb : q=b
    · subst q; simp only [Equiv.swap_apply_right,ha,hb]
    rw [Equiv.swap_apply_of_ne_of_ne qa qb]

private theorem pull_swap_invol (a b : Wire) (s : State) :
    pullState (Equiv.swap a b) (pullState (Equiv.swap a b) s)=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (Equiv.swap a b (Equiv.swap a b q))=s.basis q
    rw [Equiv.swap_apply_self]

private theorem rebind_swap_run (a b : Wire) (P : Program) (s : State) (m : List Bool)
    (ha : s.basis a=false) (hb : s.basis b=false)
    (oa : (run P m s).basis a=false) (ob : (run P m s).basis b=false) :
    run (renameProgram (Equiv.swap a b) P) m s=run P m s := by
  have eq:=ECDSAAdd.run_rename (Equiv.swap a b) (Equiv.swap a b).injective P m s
  rw [pull_swap_clean a b s ha hb,←pull_swap_clean a b (run P m s) oa ob] at eq
  have both:=congrArg (pullState (Equiv.swap a b)) eq
  simpa only [pull_swap_invol] using both

theorem first_complement (g s : Bool)
    (legal : g.toNat+2*s.toNat<3) (nonzero : g=true ∨ s=true) : g= !s := by
  cases g <;> cases s <;> simp_all

theorem run_write_outside (P : Program) (g : Wire) (off : g∉wires P)
    (s : State) (m : List Bool) (v : Bool) :
    run P m ⟨s.phase,writeBit s.basis g v⟩=
      ⟨(run P m s).phase,writeBit (run P m s).basis g v⟩ := by
  let t : State := ⟨s.phase,writeBit s.basis g v⟩
  have agrees := pool_run_agrees P (wires P) (Finset.Subset.refl _) m t s rfl (by
    intro q hq
    have ne : q≠g := fun eq => off (eq ▸ hq)
    simp only [t,writeBit,Function.update_of_ne ne])
  apply State.extensionality
  · exact agrees.1
  · funext q
    change (run P m t).basis q=writeBit (run P m s).basis g v q
    by_cases eq : q=g
    · subst q
      simpa only [t,writeBit,Function.update_self] using run_preserves_outside P m t g off
    have update : writeBit (run P m s).basis g v q=(run P m s).basis q := by
      simp only [writeBit,Function.update_of_ne eq]
    rw [update]
    by_cases used : q∈wires P
    · exact agrees.2 q used
    · have left := run_preserves_outside P m t q used
      have right := run_preserves_outside P m s q used
      have middle : t.basis q=s.basis q := by
        simp only [t,writeBit,Function.update_of_ne eq]
      exact left.trans (middle.trans right.symm)

theorem expose_run (j g : Wire) (s : State) (m : List Bool) :
    run (expose j g) m s=⟨s.phase,writeBit s.basis g (!(s.basis g ^^ s.basis j))⟩ := by
  apply State.extensionality
  · simp only [expose,run]
  · funext q
    by_cases eq : q=g
    · subst q; simp [expose,run,writeBit]
    · simp [expose,run,writeBit,eq]

theorem restore_run (j g : Wire) (ne : j≠g) (s : State) (m : List Bool) :
    run (restore j g) m s=⟨s.phase,writeBit s.basis g ((!s.basis g) ^^ s.basis j)⟩ := by
  apply State.extensionality
  · simp only [restore,run]
  · funext q
    by_cases eq : q=g
    · subst q; simp [restore,run,writeBit,ne]
    · simp [restore,run,writeBit,ne,eq]

/-- Complete-State equality for each arbitrary record tape.
Legality and the nonzero first trit are not inferred from an arbitrary frame. -/
theorem run_eq (j g carry : Wire) (P : Program) (s : State) (m : List Bool)
    (jg : j≠g) (cg : carry≠g)
    (off : g∉wires P) (keep : (run P m s).basis j=s.basis j)
    (clean : s.basis carry=false) (out : (run P m s).basis carry=false)
    (legal : (s.basis g).toNat+2*(s.basis j).toNat<3)
    (nonzero : s.basis g=true ∨ s.basis j=true) :
    run (program j g carry P) m s=run P m s := by
  have complement := first_complement (s.basis g) (s.basis j) legal nonzero
  let t : State := ⟨s.phase,writeBit s.basis g false⟩
  have start : run (expose j g) m s=t := by
    rw [expose_run,complement]
    cases bit : s.basis j <;> simp [t]
  have shifted : run P m t=
      ⟨(run P m s).phase,writeBit (run P m s).basis g false⟩ :=
    run_write_outside P g off s m false
  have tc : t.basis carry=false := by simp only [t,writeBit,Function.update_of_ne cg,clean]
  have tg : t.basis g=false := by simp only [t,writeBit,Function.update_self]
  have oc : (run P m t).basis carry=false := by
    rw [shifted]
    simp only [writeBit,Function.update_of_ne cg,out]
  have og : (run P m t).basis g=false :=
    (run_preserves_outside P m t g off).trans tg
  have rebound := rebind_swap_run carry g P t m tc tg oc og
  have finish : run (restore j g) (m.drop (measurementCount P)) (run P m t)=run P m s := by
    rw [shifted,restore_run j g jg]
    have target : (run P m s).basis g= !((run P m s).basis j) :=
      (run_preserves_outside P m s g off).trans (complement.trans (congrArg Bool.not keep.symm))
    apply State.extensionality
    · rfl
    · funext q
      by_cases eq : q=g
      · subst q
        simp only [writeBit,Function.update_self,Function.update_of_ne jg,
          Bool.not_false,Bool.true_xor,target]
      · simp only [writeBit,Function.update_of_ne eq]
  have em : measurementCount (expose j g)=0 := rfl
  have count := (renameProgram_counts (Equiv.swap carry g) P).2
  have reboundTake : run (renameProgram (Equiv.swap carry g) P)
      (m.take (measurementCount P)) t=run P m t := by
    rw [←count,run_take]
    exact rebound
  simp only [program,List.append_assoc,run_append,em,List.take_zero,List.drop_zero,
    count]
  have begin0 : run (expose j g) [] s=t := by
    rw [←run_take (expose j g) m s,em,List.take_zero] at start
    exact start
  rw [begin0,reboundTake]
  exact finish

theorem counts (j g carry : Wire) (P : Program) :
    toffoliCount (program j g carry P)=toffoliCount P ∧
      measurementCount (program j g carry P)=measurementCount P := by
  have old:=renameProgram_counts (Equiv.swap carry g) P
  simpa only [program,expose,restore,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,Nat.zero_add,Nat.add_zero] using old

theorem slots (j g carry : Wire) (P : Program) :
    gateSlots (program j g carry P)=gateSlots P+4 := by
  simp only [program,expose,restore,gateSlots_append,Baselines.rename_gateSlots,
    gateSlots_cons,gateSlots_nil,instructionSlots]
  omega

theorem physical (j g carry : Wire) (P : Program) (jg : j≠g) (hp : GatePhysical P) :
    GatePhysical (program j g carry P) := by
  have a : GatePhysical (expose j g) := by simp [expose,GatePhysical,PhysicalInstr,ProperGate,jg]
  have b : GatePhysical (restore j g) := by simp [restore,GatePhysical,PhysicalInstr,ProperGate,jg]
  simpa only [program,gatePhysical_append] using And.intro
    (And.intro a (gatePhysical_rename _ (Equiv.swap carry g).injective _ hp)) b

theorem support (j g carry : Wire) (P : Program) :
    wires (program j g carry P)⊆{j,g}∪(wires P).image (Equiv.swap carry g) := by
  simp [program,expose,restore,wires_append,renameProgram_support,wires,Instr.wires]

theorem avoids_carry (j g carry : Wire) (P : Program)
    (cj : carry≠j) (cg : carry≠g) (off : g∉wires P) :
    carry∉wires (program j g carry P) := by
  intro used
  rcases Finset.mem_union.mp (support j g carry P used) with h|h
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    exact h.elim cj cg
  · obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp h
    have same : a=g := (Equiv.swap carry g).injective (eq.trans (Equiv.swap_apply_right carry g).symm)
    exact off (same ▸ ha)

theorem support_to (j g carry : Wire) (P : Program) (S : Finset Wire)
    (old : wires P⊆S) (hj : j∈S) (hg : g∈S)
    (cj : carry≠j) (cg : carry≠g) (off : g∉wires P) :
    wires (program j g carry P)⊆S.erase carry := by
  intro q used
  have away : q≠carry := fun eq => avoids_carry j g carry P cj cg off (eq ▸ used)
  refine Finset.mem_erase.mpr ⟨away,?_⟩
  rcases Finset.mem_union.mp (support j g carry P used) with h|h
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl <;> assumption
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    by_cases ac : a=carry
    · subst a; simpa only [Equiv.swap_apply_left] using hg
    have ag : a≠g := fun eq => off (eq ▸ ha)
    simpa only [Equiv.swap_apply_of_ne_of_ne ac ag] using old ha

theorem avoids_other (j g carry q : Wire) (P : Program)
    (qj : q≠j) (qg : q≠g) (qc : q≠carry) (off : q∉wires P) :
    q∉wires (program j g carry P) := by
  intro used
  rcases Finset.mem_union.mp (support j g carry P used) with h|h
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    exact h.elim qj qg
  · obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp h
    have fix : Equiv.swap carry g q=q := Equiv.swap_apply_of_ne_of_ne qc qg
    exact off ((Equiv.swap carry g).injective (eq.trans fix.symm) ▸ ha)

/-- A caller can use its old full frame without unfolding the concrete program. -/
theorem pair_frame_eq (r y : List Wire) (origin : BasisState) (I V A B : Nat)
    (j g carry : Wire) (P : Program)
    (jg : j≠g) (cg : carry≠g)
    (ja : j∉r ∧ j∉y) (ga : g∉r ∧ g∉y) (ca : carry∉r ∧ carry∉y)
    (off : g∉wires P) (zero : origin carry=false)
    (legal : (origin g).toNat+2*(origin j).toNat<3)
    (nonzero : origin g=true ∨ origin j=true)
    (correct : Triple (PairFrame r y origin I V) P (PairFrame r y origin A B))
    (s : State) (m : List Bool) (input : PairFrame r y origin I V s.basis) :
    run (program j g carry P) m s=run P m s := by
  have output:=correct s m input
  have ji:=input.2.2 j ja.1 ja.2
  have gi:=input.2.2 g ga.1 ga.2
  apply run_eq j g carry P s m jg cg off
  · exact (output.2.2.2 j ja.1 ja.2).trans ji.symm
  · exact (input.2.2 carry ca.1 ca.2).trans zero
  · exact (output.2.2.2 carry ca.1 ca.2).trans zero
  · simpa only [gi,ji] using legal
  · simpa only [gi,ji] using nonzero

theorem pair_frame (r y : List Wire) (origin : BasisState) (I V A B : Nat)
    (j g carry : Wire) (P : Program)
    (jg : j≠g) (cg : carry≠g)
    (ja : j∉r ∧ j∉y) (ga : g∉r ∧ g∉y) (ca : carry∉r ∧ carry∉y)
    (off : g∉wires P) (zero : origin carry=false)
    (legal : (origin g).toNat+2*(origin j).toNat<3)
    (nonzero : origin g=true ∨ origin j=true)
    (correct : Triple (PairFrame r y origin I V) P (PairFrame r y origin A B)) :
    Triple (PairFrame r y origin I V) (program j g carry P) (PairFrame r y origin A B) := by
  intro s m input
  rw [pair_frame_eq r y origin I V A B j g carry P jg cg ja ga ca off zero legal nonzero correct s m input]
  exact correct s m input

end ECDSAAdd.Entrant.G0CarryLoan5
