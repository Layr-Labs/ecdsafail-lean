import ECDSAAdd.Submission.Entrant.MeasuredZeroClear

namespace ECDSAAdd.Entrant.CodexAffineGadget
open Arithmetic RecordedQuantum Challenge Baselines

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def view (a b : Wire) : Program := [.CX a b, .X b]
def restore (a b : Wire) : Program := [.X b, .CX a b]
def core (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ equalConstant b f (zeroPorts r work) k
def program (a b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view a b ++ core b f r work k ++ restore a b
def clearCore (b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  [.X f] ++ MeasuredZeroClear.equalClear b f (zeroPorts r work) k
def clearProgram (a b f : Wire) (r work : List Wire) (k : Nat) : Program :=
  view a b ++ clearCore b f r work k ++ restore a b

theorem run_concat (P Q : Program) (m : List Bool) (s : State) :
    run (P ++ Q) m s = run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append, run_take]

theorem ports_length (r work : List Wire) (hl : r.length = work.length) :
    (zeroPorts r work).length = r.length := by
  have h := congrArg List.length (zeroPorts_maps r work hl).1
  simpa using h

theorem ports_nodup (a b f : Wire) (r work : List Wire)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    (b :: f :: (zeroPorts r work).flatMap ZeroBit.wires).Nodup := by
  exact (((zeroPorts_perm r work hl).cons f).cons b).nodup_iff.mpr
    (List.nodup_cons.mp hn).2

theorem view_run (a b : Wire) (_hab : a ≠ b) (s : State) (m : List Bool) :
    run (view a b) m s =
      ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ s.basis a))⟩ := by
  simp [view, run, writeBit]

theorem restore_update (a b f : Wire) (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f)
    (s : State) (m : List Bool) (z : Bool) :
    run (restore a b) m
      ⟨s.phase, writeBit (writeBit s.basis b (!(s.basis b ^^ s.basis a))) f z⟩ =
      ⟨s.phase, writeBit s.basis f z⟩ := by
  simp only [restore, run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = b
  · subst q
    cases ha : s.basis a <;> cases hb : s.basis b <;>
      simp [writeBit, hab, haf, hbf, ha, hb]
  · by_cases hqf : q = f
    · subst q
      simp [writeBit, hab, haf, hbf, hbf.symm]
    · simp [writeBit, hq, hqf, hab, haf, hbf]

theorem program_run (a b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (a :: b :: f :: (r ++ work)).Nodup) (hl : r.length = work.length)
    (hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0) :
    run (program a b f r work k) m s =
      ⟨s.phase, writeBit s.basis f
        (s.basis f ^^ !((!(s.basis b ^^ s.basis a)) && decide (regValue r s.basis = k)))⟩ := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have hab : a ≠ b := sep.1.1
  have haf : a ≠ f := sep.1.2.1
  have hbf : b ≠ f := sep.2.1.1
  have hbr : b ∉ r := sep.2.1.2.1
  have hbw : b ∉ work := sep.2.1.2.2
  have hfr : f ∉ r := sep.2.2.1.1
  have hfw : f ∉ work := sep.2.2.1.2
  let u : State := ⟨s.phase, writeBit s.basis b (!(s.basis b ^^ s.basis a))⟩
  let v : State := ⟨s.phase, writeBit u.basis f (!s.basis f)⟩
  have hu : run (view a b) m s = u := view_run a b hab s m
  have uv : run [.X f] m u = v := by simp [run, u, v, writeBit, hbf.symm]
  have hports := zeroPorts_maps r work hl
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← hports.2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    simpa [v, u, writeBit, neb, nef] using (regValue_zero work s.basis).mp hz p.work mem
  have hr : regValue r v.basis = regValue r s.basis := by
    apply regValue_congr
    intro q hq
    simp [v, u, writeBit, show q ≠ b from fun e => hbr (e ▸ hq),
      show q ≠ f from fun e => hfr (e ▸ hq)]
  have eq := equalConstant_correct b f (zeroPorts r work) k (ports_nodup a b f r work hl hn)
    (by simpa only [ports_length r work hl] using hk) v m clean
  rw [hports.1, hr] at eq
  have vb : v.basis b = !(s.basis b ^^ s.basis a) := by simp [v, u, writeBit, hbf]
  have vf : v.basis f = !s.basis f := by simp [v, writeBit]
  rw [vb, vf] at eq
  have folded : ((!s.basis f) ^^
      (!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k))) =
      (s.basis f ^^ !(!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k))) := by
    cases s.basis f <;> cases (!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k)) <;> rfl
  rw [folded] at eq
  have shape : run (program a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, hu, uv]
  rw [shape, eq]
  simpa only [v, u, writeBit, Function.update_idem] using
    restore_update a b f hab haf hbf s (m.drop (zeroPorts r work).length)
      (s.basis f ^^ !(!(s.basis b ^^ s.basis a) && decide (regValue r s.basis = k)))

theorem program_counts (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (program a b f r work k) = r.length ∧
    measurementCount (program a b f r work k) = r.length := by
  simp [program, core, view, restore, toffoliCount_append, measurementCount_append,
    equalConstant_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem clearProgram_counts (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    toffoliCount (clearProgram a b f r work k) = r.length - 1 ∧
    measurementCount (clearProgram a b f r work k) = r.length := by
  simp [clearProgram, clearCore, view, restore, toffoliCount_append, measurementCount_append,
    MeasuredZeroClear.equal_counts, ports_length r work hl, toffoliCount, measurementCount]

theorem program_support (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    wires (program a b f r work k) ⊆ (a :: b :: f :: (r ++ work)).toFinset := by
  intro q hq
  have hp : q ∈ (zeroPorts r work).flatMap ZeroBit.wires ↔ q ∈ r ++ work :=
    (zeroPorts_perm r work hl).mem_iff
  simp only [program, core, view, restore, wires_append, equalConstant_wires, wires,
    Instr.wires, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty, or_false, List.mem_toFinset, List.mem_cons, hp] at hq ⊢
  tauto

theorem clearProgram_support (a b f : Wire) (r work : List Wire) (k : Nat) :
    wires (clearProgram a b f r work k) ⊆ wires (program a b f r work k) := by
  simp only [clearProgram, clearCore, program, core, wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union (Finset.Subset.refl _)
        (MeasuredZeroClear.equal_support b f (zeroPorts r work) k)))
    (Finset.Subset.refl _)

theorem clearProgram_run_eq (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup)
    (s : State) (m : List Bool) (hz : regValue work s.basis = 0)
    (hzero : (run (program a b f r work k) m s).basis f = false) :
    run (clearProgram a b f r work k) m s = run (program a b f r work k) m s := by
  have sep := hn
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at sep
  have haf : a ≠ f := sep.1.2.1
  have hbf : b ≠ f := sep.2.1.1
  have haw : a ∉ work := sep.1.2.2.2
  have hbw : b ∉ work := sep.2.1.2.2
  have hfw : f ∉ work := sep.2.2.1.2
  let v := run [Instr.X f] m (run (view a b) m s)
  have clean : ∀ p ∈ zeroPorts r work, v.basis p.work = false := by
    intro p hp
    have mem : p.work ∈ work := by
      rw [← (zeroPorts_maps r work hl).2]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have nea : p.work ≠ a := fun e => haw (e ▸ mem)
    have neb : p.work ≠ b := fun e => hbw (e ▸ mem)
    have nef : p.work ≠ f := fun e => hfw (e ▸ mem)
    have away : p.work ∉ wires (view a b) := by simp [view, wires, Instr.wires, nea, neb]
    change (run [Instr.X f] m (run (view a b) m s)).basis p.work = false
    rw [run_preserves_outside _ _ _ _ (by simp [wires, Instr.wires, nef]),
      run_preserves_outside _ _ _ _ away]
    exact (regValue_zero work s.basis).mp hz p.work mem
  have oldShape : run (program a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (equalConstant b f (zeroPorts r work) k) m v) := by
    simp only [program, core, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (equalConstant_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have newShape : run (clearProgram a b f r work k) m s =
      run (restore a b) (m.drop (zeroPorts r work).length)
        (run (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) m v) := by
    simp only [clearProgram, clearCore, run_concat, measurementCount_append,
      show measurementCount (view a b) = 0 from rfl,
      show measurementCount [Instr.X f] = 0 from rfl,
      (MeasuredZeroClear.equal_counts b f (zeroPorts r work) k).2,
      Nat.zero_add, List.drop_zero, v]
  have away : f ∉ wires (restore a b) := by
    simp [restore, wires, Instr.wires, haf.symm, hbf.symm]
  have keep := run_preserves_outside (restore a b) (m.drop (zeroPorts r work).length)
    (run (equalConstant b f (zeroPorts r work) k) m v) f away
  have zero : (run (equalConstant b f (zeroPorts r work) k) m v).basis f = false := by
    rw [oldShape] at hzero
    exact keep.symm.trans hzero
  have eq := MeasuredZeroClear.equal_run_eq b f (zeroPorts r work) k
    (ports_nodup a b f r work hl hn) v m clean zero
  rw [oldShape, newShape, eq]

theorem clearProgram_eq (a b f : Wire) (r work : List Wire) (k : Nat)
    (hn : (a :: b :: f :: (r ++ work)).Nodup) (hl : r.length = work.length)
    (_hk : k < 2 ^ r.length) (s : State) (m : List Bool)
    (hz : regValue work s.basis = 0)
    (hzero : (run (program a b f r work k) m s).basis f = false) :
    run (clearProgram a b f r work k) m s = run (program a b f r work k) m s :=
  clearProgram_run_eq a b f r work k hl hn s m hz hzero

theorem program_physical (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    GatePhysical (program a b f r work k) := by
  have hab : a ≠ b := by
    intro e
    exact (List.nodup_cons.mp hn).1 (by simp [e])
  have hv : GatePhysical (view a b) := by simp [view, GatePhysical, PhysicalInstr, ProperGate, hab]
  have hr : GatePhysical (restore a b) := by simp [restore, GatePhysical, PhysicalInstr, ProperGate, hab]
  simp only [program, core, gatePhysical_append]
  exact ⟨⟨hv, ⟨by simp [GatePhysical, PhysicalInstr, ProperGate],
    equalConstant_physical b f (zeroPorts r work) k (ports_nodup a b f r work hl hn)⟩⟩, hr⟩

theorem clearProgram_physical (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) (hn : (a :: b :: f :: (r ++ work)).Nodup) :
    GatePhysical (clearProgram a b f r work k) := by
  have old := program_physical a b f r work k hl hn
  simp only [program, core, gatePhysical_append] at old
  simp only [clearProgram, clearCore, gatePhysical_append]
  exact ⟨⟨old.1.1, ⟨old.1.2.1,
    MeasuredZeroClear.equal_physical b f (zeroPorts r work) k
      (ports_nodup a b f r work hl hn)⟩⟩, old.2⟩

theorem program_slots (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (program a b f r work k) ≤ 9 * r.length + 6 := by
  have h := equalConstant_gateSlots_le b f (zeroPorts r work) k
  rw [ports_length r work hl] at h
  simp only [program, core, view, restore, gateSlots_append] at *
  change 2 + (1 + gateSlots (equalConstant b f (zeroPorts r work) k)) + 2 ≤ _
  omega

theorem clearProgram_slots_le (a b f : Wire) (r work : List Wire) (k : Nat) :
    gateSlots (clearProgram a b f r work k) ≤ gateSlots (program a b f r work k) := by
  have h : gateSlots (MeasuredZeroClear.equalClear b f (zeroPorts r work) k) ≤
      gateSlots (equalConstant b f (zeroPorts r work) k) := by
    by_cases he : zeroPorts r work = []
    · rw [he]
      exact Nat.le_refl _
    · have h := MeasuredZeroClear.equal_slots b f (zeroPorts r work) k he
      omega
  simp only [clearProgram, clearCore, program, core, gateSlots_append]
  omega

theorem clearProgram_slots (a b f : Wire) (r work : List Wire) (k : Nat)
    (hl : r.length = work.length) :
    gateSlots (clearProgram a b f r work k) ≤ 9 * r.length + 6 :=
  (clearProgram_slots_le a b f r work k).trans (program_slots a b f r work k hl)

end ECDSAAdd.Entrant.CodexAffineGadget
