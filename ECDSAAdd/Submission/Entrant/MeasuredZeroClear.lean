import ECDSAAdd.Baselines.SlotAlgebra
import ECDSAAdd.Arithmetic.PointFixedPrimitivesPhysical

namespace ECDSAAdd.Entrant.MeasuredZeroClear
open Arithmetic Challenge Baselines RecordedQuantum
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def compute (c a t : Wire) : Program := [.X a, .CCX c a t, .X a]
def erase (c a t : Wire) : Program := [.X a, .measureX t [] [.CZ c a], .X a]

def zeroClear (c target : Wire) : List ZeroBit → Program
  | [] => [.CX c target]
  | [b] => erase c b.input target
  | b::d::bs => compute c b.input b.work ++ zeroClear b.work target (d::bs) ++ erase c b.input b.work

theorem old_cons (c t : Wire) (b : ZeroBit) (bs : List ZeroBit) :
    zeroControlled c t (b::bs) =
      compute c b.input b.work ++ zeroControlled b.work t bs ++ erase c b.input b.work := rfl

theorem compute_run (c a t : Wire) (hca : c≠a) (hat : a≠t) (s : State) (m : List Bool) :
    run (compute c a t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis a))⟩ := by
  simp only [compute,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=a
  · subst w; simp [writeBit,hca,hat]
  · by_cases ht : w=t
    · subst w; simp [writeBit,hca,Ne.symm hat]
    · simp [writeBit,hw,ht,hca]

theorem erase_run (c a t : Wire) (hca : c≠a) (hat : a≠t) (hct : c≠t)
    (s : State) (m : List Bool) (hq : s.basis t = (s.basis c && !s.basis a)) :
    run (erase c a t) m s = ⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [erase,run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect,correct,writeBit,hca,hat,hat.symm,hct,hq]
  all_goals
    funext w
    by_cases hw : w=a
    · subst w; simp [hat]
    · simp [Function.update_apply,hw]

theorem counts (c t : Wire) (bs : List ZeroBit) :
    toffoliCount (zeroClear c t bs)=bs.length-1 ∧
    measurementCount (zeroClear c t bs)=bs.length := by
  induction bs generalizing c with
  | nil => simp [zeroClear,toffoliCount,measurementCount]
  | cons b bs ih =>
    cases bs with
    | nil => simp [zeroClear,erase,toffoliCount,measurementCount]
    | cons d ds =>
      simp only [zeroClear,toffoliCount_append,measurementCount_append,ih]
      simp [compute,erase,toffoliCount,measurementCount]
      omega

theorem support (c t : Wire) (bs : List ZeroBit) :
    wires (zeroClear c t bs) ⊆ wires (zeroControlled c t bs) := by
  induction bs generalizing c with
  | nil => exact Finset.Subset.refl _
  | cons b bs ih =>
    cases bs with
    | nil =>
      rw [zeroControlled_wires]
      intro q h
      simp [zeroClear,erase,wires,Instr.wires,correctionWires,ZeroBit.wires] at h ⊢
      tauto
    | cons d ds =>
      rw [zeroClear,old_cons,wires_append,wires_append,wires_append,wires_append]
      exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) (ih _))
        (Finset.Subset.refl _)

theorem slots (c t : Wire) (bs : List ZeroBit) (hne : bs≠[]) :
    gateSlots (zeroClear c t bs)+4=gateSlots (zeroControlled c t bs) := by
  induction bs generalizing c with
  | nil => exact False.elim (hne rfl)
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons d ds =>
      rw [zeroClear,old_cons]
      simp only [gateSlots_append]
      have h := ih b.work (by simp)
      omega

theorem run_eq (c target : Wire) (bs : List ZeroBit)
    (hnd : (c::target::bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀b∈bs,s.basis b.work=false)
    (hzero : (run (zeroControlled c target bs) m s).basis target=false) :
    run (zeroClear c target bs) m s=run (zeroControlled c target bs) m s := by
  induction bs generalizing c s m with
  | nil => rfl
  | cons b bs ih =>
    have hnames : (c::target::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hnd
    have hni := hnames
    simp only [List.nodup_cons,List.mem_cons,not_or] at hni
    have hca : c≠b.input := hni.1.2.1
    have hai : b.input≠b.work := hni.2.2.1.1
    have hta : target≠b.input := hni.2.1.1
    have htw : target≠b.work := hni.2.1.2.1
    have hcw : c≠b.work := hni.1.2.2.1
    have hct : c≠target := hni.1.1
    cases bs with
    | nil =>
      have old := zeroControlled_correct c target [b] hnd s m hz
      have ht : s.basis target = (s.basis c && !s.basis b.input) := by
        simpa [old,writeBit] using hzero
      rw [zeroClear,erase_run c b.input target hca hta.symm hct s m ht,old]
      simp [ht]
    | cons d ds =>
      have hchild : (b.work::target::(d::ds).flatMap ZeroBit.wires).Nodup := by
        simp only [List.nodup_cons,List.mem_cons,not_or]
        exact ⟨⟨htw.symm,hni.2.2.2.1⟩,hni.2.1.2.2,hni.2.2.2.2⟩
      let u := run (compute c b.input b.work) m s
      have hu := compute_run c b.input b.work hca hai s m
      have hz' : ∀e∈d::ds,u.basis e.work=false := by
        intro e he
        have ne : e.work≠b.work := by
          intro eq
          exact hni.2.2.2.1 (List.mem_flatMap.mpr ⟨e,he,by simp [ZeroBit.wires,eq]⟩)
        simpa [u,hu,writeBit,ne] using hz e (by simp [he])
      have off : target∉wires (erase c b.input b.work) := by
        simp [erase,wires,Instr.wires,correctionWires,htw,hta,hct.symm]
      have zero : (run (zeroControlled b.work target (d::ds)) m u).basis target=false := by
        have keep := run_preserves_outside (erase c b.input b.work) (m.drop (d::ds).length)
          (run (zeroControlled b.work target (d::ds)) m u) target off
        rw [old_cons,run_append,run_take,run_append,run_take] at hzero
        simp only [measurementCount_append,show measurementCount (compute c b.input b.work)=0 from rfl,
          (zeroControlled_counts b.work target (d::ds)).2,Nat.zero_add,List.drop_zero] at hzero
        exact keep.symm.trans hzero
      rw [zeroClear,old_cons,run_append,run_take,run_append,run_take,
        run_append,run_take,run_append,run_take]
      simp only [measurementCount_append,show measurementCount (compute c b.input b.work)=0 from rfl,
        (counts b.work target (d::ds)).2,(zeroControlled_counts b.work target (d::ds)).2,
        Nat.zero_add,List.drop_zero]
      rw [ih b.work hchild u m hz' zero]

theorem physical (c target : Wire) (bs : List ZeroBit)
    (hn : (c::target::bs.flatMap ZeroBit.wires).Nodup) : GatePhysical (zeroClear c target bs) := by
  induction bs generalizing c with
  | nil => exact zeroControlled_physical c target [] hn
  | cons b bs ih =>
    have names : (c::target::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hn
    have h := names
    simp only [List.nodup_cons,List.mem_cons,not_or] at h
    cases bs with
    | nil => simp [zeroClear,erase,GatePhysical,PhysicalInstr,ProperGate]
    | cons d ds =>
      have child : (b.work::target::(d::ds).flatMap ZeroBit.wires).Nodup := by
        simp only [List.nodup_cons,List.mem_cons,not_or]
        exact ⟨⟨Ne.symm h.2.1.2.1,h.2.2.2.1⟩,h.2.1.2.2,h.2.2.2.2⟩
      have old := zeroControlled_physical c target (b::d::ds) hn
      rw [old_cons,gatePhysical_append,gatePhysical_append] at old
      rw [zeroClear,gatePhysical_append,gatePhysical_append]
      exact ⟨⟨old.1.1,ih _ child⟩,old.2⟩

def equalClear (c t : Wire) (bs : List ZeroBit) (k : Nat) : Program :=
  xorConstant (bs.map ZeroBit.input) k ++ zeroClear c t bs ++ xorConstant (bs.map ZeroBit.input) k

theorem equal_counts (c t : Wire) (bs : List ZeroBit) (k : Nat) :
    toffoliCount (equalClear c t bs k)=bs.length-1 ∧
    measurementCount (equalClear c t bs k)=bs.length := by
  simp [equalClear,toffoliCount_append,measurementCount_append,xorConstant_counts,counts]

theorem equal_support (c t : Wire) (bs : List ZeroBit) (k : Nat) :
    wires (equalClear c t bs k) ⊆ wires (equalConstant c t bs k) := by
  simp only [equalClear,equalConstant,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) (support _ _ _))
    (Finset.Subset.refl _)

theorem equal_slots (c t : Wire) (bs : List ZeroBit) (k : Nat) (hne : bs≠[]) :
    gateSlots (equalClear c t bs k)+4=gateSlots (equalConstant c t bs k) := by
  have h := slots c t bs hne
  simp only [equalClear,equalConstant,gateSlots_append]
  omega

theorem equal_physical (c t : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (c::t::bs.flatMap ZeroBit.wires).Nodup) : GatePhysical (equalClear c t bs k) := by
  simp only [equalClear,gatePhysical_append]
  exact ⟨⟨xorConstant_physical _ _,physical _ _ _ hn⟩,xorConstant_physical _ _⟩

private theorem split_count (bs : List ZeroBit) (q : Wire) :
    (bs.flatMap ZeroBit.wires).count q=(bs.map ZeroBit.input).count q+(bs.map ZeroBit.work).count q := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons,ZeroBit.wires,List.map_cons,List.count_append,List.count_cons,List.count_nil,ih]
    omega

theorem equal_run_eq (c t : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (c::t::bs.flatMap ZeroBit.wires).Nodup) (s : State) (m : List Bool)
    (hz : ∀b∈bs,s.basis b.work=false)
    (hzero : (run (equalConstant c t bs k) m s).basis t=false) :
    run (equalClear c t bs k) m s=run (equalConstant c t bs k) m s := by
  let src := bs.map ZeroBit.input
  let P := xorConstant src k
  let u := run P m s
  have off : t∉wires P := by
    intro ht
    have mem := List.mem_toFinset.mp (xorConstant_wires_subset src k ht)
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp mem
    exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires,eq]⟩)
  have hz' : ∀b∈bs,u.basis b.work=false := by
    intro b hb
    have away : b.work∉wires P := by
      intro hw
      have mem := List.mem_toFinset.mp (xorConstant_wires_subset src k hw)
      have a := List.count_pos_iff.mpr mem
      have w := List.count_pos_iff.mpr (List.mem_map.mpr ⟨b,hb,rfl⟩ : b.work∈bs.map ZeroBit.work)
      have nd := List.nodup_iff_count.mp hn b.work
      have sp := split_count bs b.work
      simp only [List.count_cons] at nd
      change 0<(bs.map ZeroBit.input).count b.work at a
      omega
    exact (run_preserves_outside P m s b.work away).trans (hz b hb)
  have zero : (run (zeroControlled c t bs) m u).basis t=false := by
    have keep := run_preserves_outside P (m.drop bs.length) (run (zeroControlled c t bs) m u) t off
    rw [equalConstant,run_append,run_take,run_append,run_take] at hzero
    simp only [measurementCount_append,(xorConstant_counts _ _).2,
      (zeroControlled_counts _ _ _).2,Nat.zero_add,List.drop_zero] at hzero
    exact keep.symm.trans hzero
  rw [equalClear,equalConstant,run_append,run_take,run_append,run_take,
    run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(xorConstant_counts _ _).2,(counts c t bs).2,
    (zeroControlled_counts c t bs).2,Nat.zero_add,List.drop_zero]
  rw [run_eq c t bs hn u m hz' zero]

end ECDSAAdd.Entrant.MeasuredZeroClear
