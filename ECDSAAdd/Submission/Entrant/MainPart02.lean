import ECDSAAdd.Submission.Entrant.MainPart01

set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.LowZero18KRegs =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.DiagSquare
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero

/-! The LowZero wrappers from accepted606afa1e, with the checked old KRegs layout. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)

/-- `m8` with the dead lowest carry dropped: its source `T = 2ab` is even and `cin` is clean. -/
def m8z : Program := LowZero.addLow0 (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin

theorem m8z_lens (w : R.W) : (R.T++R.zM).length=R.dmid.length ∧
    (R.carry.take (R.dmid.length-1)).length+1=R.dmid.length ∧ 2≤R.dmid.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega

theorem m8z_counts (w : R.W) : toffoliCount R.m8z+1=toffoliCount R.m8 ∧
    measurementCount R.m8z=measurementCount R.m8 := by
  have l := R.m8z_lens w
  exact LowZero.addLow0_counts_rel _ _ _ _ l.1 l.2.1 l.2.2

theorem m8z_wires (w : R.W) : wires R.m8z⊆wires R.m8 := by
  have l := R.m8z_lens w
  exact LowZero.addLow0_wires_sub _ _ _ _ l.1 l.2.1 l.2.2

theorem m8z_slots (w : R.W) : Challenge.gateSlots R.m8z≤Challenge.gateSlots R.m8 := by
  have l := R.m8z_lens w
  exact LowZero.addLow0_slots _ _ _ _ l.1 l.2.1 l.2.2

theorem m8z_physical (hn : R.all.Nodup) : GatePhysical R.m8z :=
  LowZero.addLow0_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))

theorem m8z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (k : Nat)
    (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hT : regValue R.T s.basis=2*k) (hi : s.basis R.cin=false) :
    (run R.m8z m s).phase=s.phase ∧
    (∀q,q∉R.dmid → (run R.m8z m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.m8z m s).basis=
      (regValue (R.T++R.zM) s.basis+regValue R.dmid s.basis+(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8z_lens w
  have hTl := w.T; have hSl := w.S
  have ne : R.T≠[] := by
    intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
  exact LowZero.addLow0_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl (LowZero.head_false_of_even R.T R.zM s.basis k hT ne) hi

/-- `m7` (`T -= b²`) with its dead lowest carry dropped: bit 0 of `T = 2ab+b²` equals bit 0 of `b²`. -/
def m7z : Program := LowZero.subLowNC (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
/-- `c8` (`dmid -= T`) with its dead lowest carry dropped: `T = 2ab` is even. -/
def c8z : Program := LowZero.subLowNC (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
/-- `c7` (`T += b²`) with its dead lowest carry dropped: `T = 2ab` is even. -/
def c7z : Program := LowZero.addLowNC (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin

theorem t_lens (w : R.W) : (R.dhi++R.zB).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dhi++R.zB).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega

theorem T_ne (w : R.W) : R.T≠[] := by
  have hTl := w.T; have hSl := w.S
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega

theorem dhi_ne (w : R.W) : R.dhi≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega

theorem m7z_counts (w : R.W) : toffoliCount R.m7z+1=toffoliCount R.m7 ∧
    measurementCount R.m7z=measurementCount R.m7 := by
  have l := R.t_lens w
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7z_counts (w : R.W) : toffoliCount R.c7z+1=toffoliCount R.c7 ∧
    measurementCount R.c7z=measurementCount R.c7 := by
  have l := R.t_lens w
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c8z_counts (w : R.W) : toffoliCount R.c8z+1=toffoliCount R.c8 ∧
    measurementCount R.c8z=measurementCount R.c8 := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2

theorem m7z_wires (w : R.W) : wires R.m7z⊆wires R.m7 := by
  have l := R.t_lens w
  exact LowZero.subLowNC_wires_sub _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7z_wires (w : R.W) : wires R.c7z⊆wires R.c7 := by
  have l := R.t_lens w
  exact LowZero.addLowNC_wires_sub _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c8z_wires (w : R.W) : wires R.c8z⊆wires R.c8 := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_wires_sub _ _ _ _ l.1 l.2.1 l.2.2

theorem m7z_slots (w : R.W) : Challenge.gateSlots R.m7z≤Challenge.gateSlots R.m7 := by
  have l := R.t_lens w
  exact LowZero.subLowNC_slots _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7z_slots (w : R.W) : Challenge.gateSlots R.c7z≤Challenge.gateSlots R.c7 := by
  have l := R.t_lens w
  exact LowZero.addLowNC_slots _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c8z_slots (w : R.W) : Challenge.gateSlots R.c8z≤Challenge.gateSlots R.c8 := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_slots _ _ _ _ l.1 l.2.1 l.2.2

theorem m7z_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.m7z := by
  have l := R.t_lens w
  exact LowZero.subLowNC_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) l.2.2.2 (by omega)
theorem c7z_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.c7z := by
  have l := R.t_lens w
  exact LowZero.addLowNC_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) l.2.2.2 (by omega)
theorem c8z_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.c8z := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) (by omega) (by omega)

theorem m7z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m7z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7z m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7z m s).basis=
      (regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lens w
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi
theorem c8z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hnc : (s.basis ((R.T++R.zM).headD 0) && !s.basis (R.dmid.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c8z m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.c8z m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.c8z m s).basis=
      (regValue R.dmid s.basis+2^R.dmid.length-regValue (R.T++R.zM) s.basis-(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl hnc hi
theorem c7z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c7z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7z m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7z m s).basis=
      (regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lens w
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi


end ECDSAAdd.Entrant.KRegs
end -- original module boundary


section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero
open ECDSAAdd ECDSAAdd.Arithmetic
/-! ### Guarded forms

The guarded programs fall back to the untrimmed adder when the register lengths are
degenerate, so their slot bound holds without any width hypothesis. -/

def addLow0G (x y carry : List Wire) (cin : Wire) : Program :=
  if x.length = y.length ∧ carry.length + 1 = y.length ∧ 2 ≤ y.length then addLow0 x y carry cin
  else addInPlace x y carry cin
def addLowNCG (x y carry : List Wire) (cin : Wire) : Program :=
  if x.length = y.length ∧ carry.length + 1 = y.length ∧ 2 ≤ y.length then addLowNC x y carry cin
  else addInPlace x y carry cin
def subLowNCG (x y carry : List Wire) (cin : Wire) : Program :=
  if x.length = y.length ∧ carry.length + 1 = y.length ∧ 2 ≤ y.length then subLowNC x y carry cin
  else subInPlace x y carry cin

theorem addLow0G_eq (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    addLow0G x y carry cin = addLow0 x y carry cin := if_pos ⟨hx, hc, h2⟩
theorem addLowNCG_eq (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    addLowNCG x y carry cin = addLowNC x y carry cin := if_pos ⟨hx, hc, h2⟩
theorem subLowNCG_eq (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    subLowNCG x y carry cin = subLowNC x y carry cin := if_pos ⟨hx, hc, h2⟩

theorem addLow0G_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addLow0G x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  unfold addLow0G; split
  · next h => exact addLow0_slots x y carry cin h.1 h.2.1 h.2.2
  · exact le_refl _
theorem addLowNCG_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addLowNCG x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  unfold addLowNCG; split
  · next h => exact addLowNC_slots x y carry cin h.1 h.2.1 h.2.2
  · exact le_refl _
theorem subLowNCG_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (subLowNCG x y carry cin) ≤ Challenge.gateSlots (subInPlace x y carry cin) := by
  unfold subLowNCG; split
  · next h => exact subLowNC_slots x y carry cin h.1 h.2.1 h.2.2
  · exact le_refl _

theorem addLow0G_wires_sub (x y carry : List Wire) (cin : Wire) :
    wires (addLow0G x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  unfold addLow0G; split
  · next h => exact addLow0_wires_sub x y carry cin h.1 h.2.1 h.2.2
  · exact subset_refl _
theorem addLowNCG_wires_sub (x y carry : List Wire) (cin : Wire) :
    wires (addLowNCG x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  unfold addLowNCG; split
  · next h => exact addLowNC_wires_sub x y carry cin h.1 h.2.1 h.2.2
  · exact subset_refl _
theorem subLowNCG_wires_sub (x y carry : List Wire) (cin : Wire) :
    wires (subLowNCG x y carry cin) ⊆ wires (subInPlace x y carry cin) := by
  unfold subLowNCG; split
  · next h => exact subLowNC_wires_sub x y carry cin h.1 h.2.1 h.2.2
  · exact subset_refl _

theorem nodup_assoc (cin : Wire) (x y carry : List Wire) (hn : (cin :: (x ++ y ++ carry)).Nodup) :
    (cin :: x ++ y ++ carry).Nodup := by
  simpa only [List.cons_append, List.append_assoc] using hn

theorem addLow0G_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (addLow0G x y carry cin) := by
  unfold addLow0G; split
  · exact addLow0_physical x y carry cin hn
  · exact addInPlace_physical x y carry cin (nodup_assoc cin x y carry hn)
theorem addLowNCG_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (addLowNCG x y carry cin) := by
  unfold addLowNCG; split
  · next h => exact addLowNC_physical x y carry cin hn (by omega) (by omega)
  · exact addInPlace_physical x y carry cin (nodup_assoc cin x y carry hn)
theorem subLowNCG_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (subLowNCG x y carry cin) := by
  unfold subLowNCG; split
  · next h => exact subLowNC_physical x y carry cin hn (by omega) (by omega)
  · simp only [subInPlace, gatePhysical_append]
    exact ⟨⟨notRegister_physical _, addInPlace_physical x y carry cin (nodup_assoc cin x y carry hn)⟩,
      notRegister_physical _⟩

end ECDSAAdd.Entrant.LowZero

namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)
/-! Low-bit carry trims (LowZero): each `*z` program drops the dead bit-0 carry of the
corresponding Karatsuba combination adder. -/
theorem m8g_lens (w : R.W) : (R.T++R.zM).length=R.dmid.length ∧
    (R.carry.take (R.dmid.length-1)).length+1=R.dmid.length ∧ 2≤R.dmid.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
theorem t_lensg (w : R.W) : (R.dhi++R.zB).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dhi++R.zB).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega
theorem lo_lens (w : R.W) : (R.dlo++R.zA).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dlo++R.zA).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega
theorem T_neg (w : R.W) : R.T≠[] := by
  have hTl := w.T; have hSl := w.S
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
theorem dhi_neg (w : R.W) : R.dhi≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
theorem dlo_ne (w : R.W) : R.dlo≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
def m8g : Program := LowZero.addLow0G (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
theorem m8g_counts (w : R.W) : toffoliCount R.m8g+1=toffoliCount R.m8 ∧
    measurementCount R.m8g=measurementCount R.m8 := by
  have l := R.m8g_lens w
  unfold m8g; rw [LowZero.addLow0G_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.addLow0_counts_rel _ _ _ _ l.1 l.2.1 l.2.2
theorem m8g_wires : wires R.m8g⊆wires R.m8 := LowZero.addLow0G_wires_sub _ _ _ _
theorem m8g_slots : Challenge.gateSlots R.m8g≤Challenge.gateSlots R.m8 := LowZero.addLow0G_slots _ _ _ _
theorem m8g_physical (hn : R.all.Nodup) : GatePhysical R.m8g :=
  LowZero.addLow0G_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m8g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (k : Nat) (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hT : regValue R.T s.basis=2*k) (hi : s.basis R.cin=false) :
    (run R.m8g m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.m8g m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.m8g m s).basis=(regValue (R.T++R.zM) s.basis+regValue R.dmid s.basis+(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8g_lens w
  unfold m8g; rw [LowZero.addLow0G_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.addLow0_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl (LowZero.head_false_of_even R.T R.zM s.basis k hT (R.T_neg w)) hi

def m7g : Program := LowZero.subLowNCG (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m7g_counts (w : R.W) : toffoliCount R.m7g+1=toffoliCount R.m7 ∧
    measurementCount R.m7g=measurementCount R.m7 := by
  have l := R.t_lensg w
  unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem m7g_wires : wires R.m7g⊆wires R.m7 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem m7g_slots : Challenge.gateSlots R.m7g≤Challenge.gateSlots R.m7 := LowZero.subLowNCG_slots _ _ _ _
theorem m7g_physical (hn : R.all.Nodup) : GatePhysical R.m7g :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m7g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m7g m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7g m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7g m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def c8g : Program := LowZero.subLowNCG (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
theorem c8g_counts (w : R.W) : toffoliCount R.c8g+1=toffoliCount R.c8 ∧
    measurementCount R.c8g=measurementCount R.c8 := by
  have l := R.m8g_lens w
  unfold c8g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2
theorem c8g_wires : wires R.c8g⊆wires R.c8 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem c8g_slots : Challenge.gateSlots R.c8g≤Challenge.gateSlots R.c8 := LowZero.subLowNCG_slots _ _ _ _
theorem c8g_physical (hn : R.all.Nodup) : GatePhysical R.c8g :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c8g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hnc : (s.basis ((R.T++R.zM).headD 0) && !s.basis (R.dmid.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c8g m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.c8g m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.c8g m s).basis=(regValue R.dmid s.basis+2^R.dmid.length-regValue (R.T++R.zM) s.basis-(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8g_lens w
  unfold c8g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl hnc hi

def c7g : Program := LowZero.addLowNCG (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c7g_counts (w : R.W) : toffoliCount R.c7g+1=toffoliCount R.c7 ∧
    measurementCount R.c7g=measurementCount R.c7 := by
  have l := R.t_lensg w
  unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7g_wires : wires R.c7g⊆wires R.c7 := LowZero.addLowNCG_wires_sub _ _ _ _
theorem c7g_slots : Challenge.gateSlots R.c7g≤Challenge.gateSlots R.c7 := LowZero.addLowNCG_slots _ _ _ _
theorem c7g_physical (hn : R.all.Nodup) : GatePhysical R.c7g :=
  LowZero.addLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c7g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c7g m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7g m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7g m s).basis=(regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def m6z : Program := LowZero.subLowNCG (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m6z_counts (w : R.W) : toffoliCount R.m6z+1=toffoliCount R.m6 ∧
    measurementCount R.m6z=measurementCount R.m6 := by
  have l := R.lo_lens w
  unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem m6z_wires : wires R.m6z⊆wires R.m6 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem m6z_slots : Challenge.gateSlots R.m6z≤Challenge.gateSlots R.m6 := LowZero.subLowNCG_slots _ _ _ _
theorem m6z_physical (hn : R.all.Nodup) : GatePhysical R.m6z :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m6z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m6z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m6z m s).basis q=s.basis q) ∧
    regValue R.T (run R.m6z m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dlo++R.zA) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.lo_lens w
  unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def c6z : Program := LowZero.addLowNCG (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c6z_counts (w : R.W) : toffoliCount R.c6z+1=toffoliCount R.c6 ∧
    measurementCount R.c6z=measurementCount R.c6 := by
  have l := R.lo_lens w
  unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c6z_wires : wires R.c6z⊆wires R.c6 := LowZero.addLowNCG_wires_sub _ _ _ _
theorem c6z_slots : Challenge.gateSlots R.c6z≤Challenge.gateSlots R.c6 := LowZero.addLowNCG_slots _ _ _ _
theorem c6z_physical (hn : R.all.Nodup) : GatePhysical R.c6z :=
  LowZero.addLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c6z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c6z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c6z m s).basis q=s.basis q) ∧
    regValue R.T (run R.c6z m s).basis=(regValue (R.dlo++R.zA) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.lo_lens w
  unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

end ECDSAAdd.Entrant.KRegs

namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-- `rawMake` with the dead lowest carry of the first signed row copied (TrimRow), and, for odd leaves,
the dead top carry of the middle signed row copied too (TrimMid). -/
def rawMakeT (xs dst pad carry : List Wire) : Program := ECDSAAdd.Entrant.TrimMid.mkP xs dst pad carry

/-- `rawClear` with the same dead carries copied. -/
def rawClearT (xs dst pad carry : List Wire) : Program := ECDSAAdd.Entrant.TrimMid.clP xs dst pad carry

/-- Number of odd leaves (each saves one more Toffoli) among the three leaf squares of `R`. -/
def parR (R : KRegs) : Nat :=
  ECDSAAdd.Entrant.TrimMid.par R.lo.length+ECDSAAdd.Entrant.TrimMid.par R.hi.length+
    ECDSAAdd.Entrant.TrimMid.par R.S.length

theorem parR_eq (R : KRegs) (w : R.W) :
    parR R=ECDSAAdd.Entrant.TrimMid.par R.h+ECDSAAdd.Entrant.TrimMid.par (R.bank.length-R.h)+
      ECDSAAdd.Entrant.TrimMid.par (R.bank.length-R.h+1) := by
  obtain ⟨L0,L1,-⟩ := R.lens w
  rw [parR,L0,L1,w.S]

theorem rawMakeT_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawMakeT xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawMakeT xs dst pad carry) m s).basis=
      (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length ∧
    ∀q,q∉dst → (run (rawMakeT xs dst pad carry) m s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := ECDSAAdd.Entrant.TrimMid.mkP_exists xs dst pad carry hn hx hd hp hc s m h0 hp0 hc0
  rw [rawMakeT,hR]
  exact rawMake_correct xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0

theorem rawClearT_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool)
    (h0 : regValue dst s.basis=(regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawClearT xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawClearT xs dst pad carry) m s).basis=0 ∧
    ∀q,q∉dst → (run (rawClearT xs dst pad carry) m s).basis q=s.basis q := by
  let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
  have away (q : Wire) (hq : q∈xs++pad++carry) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq; have b := List.count_pos_iff.mpr bad
    simp only [List.count_append] at h a; omega
  have keep (r : List Wire) (hr : ∀q∈r,q∈xs++pad++carry) :
      regValue r base.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [base,away q (hr q hq)])
  have d0 : regValue dst base.basis=0 := (regValue_zero _ _).mpr (fun q hq => by simp [base,hq])
  have p0 := (keep pad (fun q h => by simp [h])).trans hp0
  have c0 := (keep carry (fun q h => by simp [h])).trans hc0
  have f := rawMake_correct xs dst pad carry hn hx hd hp hc base [] d0 p0 c0
  have same : run (rawMake xs dst pad carry) [] base=s := by
    apply state_ext (t:=s) (show _=s.phase from f.1)
    funext q
    by_cases hq : q∈dst
    · apply (regValue_eq_iff dst _ _).mp _ q hq
      rw [f.2.1,keep xs (fun q h => by simp [h]),h0]
    · exact (f.2.2 q hq).trans (by simp [base,hq])
  obtain ⟨R1,h1⟩ := ECDSAAdd.Entrant.TrimMid.clP_exists xs dst pad carry hn hx hd hp hc base d0 p0 c0 m
  have h1' : run (rawClearT xs dst pad carry) m s=run (ECDSAAdd.Entrant.TrimRow.cl xs dst pad carry) R1 s := by
    rw [← same]; exact h1
  obtain ⟨R,hR⟩ := ECDSAAdd.Entrant.TrimRow.cl_exists xs dst pad carry hn hx hd hp hc s R1 h0 hc0
  rw [h1',hR]
  exact rawClear_correct xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0

theorem rawT_counts (xs dst pad carry : List Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : xs.length-1≤carry.length) :
    (toffoliCount (rawMakeT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=toffoliCount (rawMake xs dst pad carry) ∧
      measurementCount (rawMakeT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=measurementCount (rawMake xs dst pad carry)) ∧
    (toffoliCount (rawClearT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=toffoliCount (rawClear xs dst pad carry) ∧
      measurementCount (rawClearT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=measurementCount (rawClear xs dst pad carry)) := by
  have a := ECDSAAdd.Entrant.TrimRow.counts xs dst pad carry hx hd hp hc
  have b := ECDSAAdd.Entrant.TrimMid.P_counts xs dst pad carry hx hd hp hc
  simp only [rawMakeT,rawClearT,rawMake,rawClear] at a b ⊢
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

theorem rawT_slots (xs dst pad carry : List Wire) :
    Challenge.gateSlots (rawMakeT xs dst pad carry)≤Challenge.gateSlots (rawMake xs dst pad carry) ∧
    Challenge.gateSlots (rawClearT xs dst pad carry)≤Challenge.gateSlots (rawClear xs dst pad carry) :=
  ⟨(ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry).1.2.1.trans (ECDSAAdd.Entrant.TrimRow.slots xs dst pad carry).1,
    (ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry).2.2.1.trans (ECDSAAdd.Entrant.TrimRow.slots xs dst pad carry).2⟩

theorem rawT_wires (xs dst pad carry : List Wire) (X : Finset Wire)
    (h1 : wires (signedSquareRows xs dst pad carry)⊆X) (h2 : wires (signedSquareTop xs dst)⊆X)
    (h3 : wires (signedSquareRowsClear xs dst pad carry)⊆X) :
    wires (rawMakeT xs dst pad carry)⊆X ∧ wires (rawClearT xs dst pad carry)⊆X := by
  have w := ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry
  have p := ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry
  simp only [wires_append] at w
  exact ⟨p.1.1.trans (w.1.trans (Finset.union_subset h1 h2)),p.2.1.trans (w.2.trans (Finset.union_subset h2 h3))⟩

theorem rawT_physical (xs dst pad carry : List Wire)
    (h1 : GatePhysical (signedSquareRows xs dst pad carry)) (h2 : GatePhysical (signedSquareTop xs dst))
    (h3 : GatePhysical (signedSquareRowsClear xs dst pad carry)) :
    GatePhysical (rawMakeT xs dst pad carry) ∧ GatePhysical (rawClearT xs dst pad carry) := by
  have t := ECDSAAdd.Entrant.TrimRow.physical xs dst pad carry
    (by rw [gatePhysical_append]; exact ⟨h1,h2⟩) (by rw [gatePhysical_append]; exact ⟨h2,h3⟩)
  have p := ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry
  exact ⟨p.1.2.2 t.1,p.2.2.2 t.2⟩


def seedsT (R : KRegs) : Program :=
  rawMakeT R.lo R.dlo R.pad R.carry ++ rawMakeT R.hi R.dhi R.pad R.carry ++ R.smk ++
    rawMakeT R.S R.T R.pad R.carry

theorem seedsT_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (seedsT R) m s)
      (vec (rawValue R.h (regValue R.lo s.basis)) (rawValue R.h (regValue R.hi s.basis))
        (regValue R.lo s.basis+regValue R.hi s.basis)
        (rawValue (R.h+1) (regValue R.lo s.basis+regValue R.hi s.basis))) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry; have hpl := w.pad
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have init : Shape R s s (vec 0 0 0 0) := by
    refine ⟨rfl,?_,fun _ _ _ _ => rfl⟩
    intro i; fin_cases i
    · change (regValue R.dlo s.basis : Int) ≡ 0 [ZMOD _]
      rw [KRegs.xz (r:=R.dlo) hd0 (fun q h => List.mem_of_mem_take h)]; rfl
    · change (regValue R.dhi s.basis : Int) ≡ 0 [ZMOD _]
      rw [KRegs.xz (r:=R.dhi) hd0 (fun q h => List.mem_of_mem_drop h)]; rfl
    · change (regValue R.S s.basis : Int) ≡ 0 [ZMOD _]
      rw [hS0]; rfl
    · change (regValue R.T s.basis : Int) ≡ 0 [ZMOD _]
      rw [hT0]; rfl
  have loStep : Transition R s (vec 0 0 0 0) (vec (rawValue R.h a) 0 0 0)
      (rawMakeT R.lo R.dlo R.pad R.carry) := by
    intro t rec ht
    have lt := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have r := rawMakeT_correct R.lo R.dlo R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 0 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 0) (run (rawMakeT R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h a : Nat) [ZMOD (2^(reg R 0).length : Nat)] := by
      change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,lt,L0]; rfl
    simpa only [vec0] using ht.step hn 0 (rawValue R.h a) r.1 r.2.2 v
  have hiStep : Transition R s (vec (rawValue R.h a) 0 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) 0 0) (rawMakeT R.hi R.dhi R.pad R.carry) := by
    intro t rec ht
    have ht0 := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := rawMakeT_correct R.hi R.dhi R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 1 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 1) (run (rawMakeT R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h b : Nat) [ZMOD (2^(reg R 1).length : Nat)] := by
      change (regValue R.dhi _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,ht0,hhi]; rfl
    simpa only [vec1] using ht.step hn 1 (rawValue R.h b) r.1 r.2.2 v
  have sumStep : Transition R s (vec (rawValue R.h a) (rawValue R.h b) 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) (a+b) 0) R.smk := by
    intro t rec ht
    have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := R.smk_correct w hn t rec (ht.exact 2 0 rfl (by norm_num))
      ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
    have v : (regValue (reg R 2) (run R.smk rec t).basis : Int) ≡ (a+b : Nat) [ZMOD (2^(reg R 2).length : Nat)] := by
      change (regValue R.S _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,al,bl]
    simpa only [vec2] using ht.step hn 2 (a+b : Nat) r.1 r.2.2 v
  have sqStep : Transition R s (vec (rawValue R.h a) (rawValue R.h b) (a+b) 0)
      (vec (rawValue R.h a) (rawValue R.h b) (a+b) (rawValue (R.h+1) (a+b)))
      (rawMakeT R.S R.T R.pad R.carry) := by
    intro t rec ht
    have av := regValue_lt R.lo s.basis
    have bv := regValue_lt R.hi s.basis
    rw [L0] at av; rw [hhi] at bv
    have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
    have sv := ht.exact 2 (a+b) rfl slt
    change regValue R.S t.basis=a+b at sv
    have r := rawMakeT_correct R.S R.T R.pad R.carry
      (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
      (by omega) hTl hpl (by omega) t rec
      (ht.exact 3 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 3) (run (rawMakeT R.S R.T R.pad R.carry) rec t).basis : Int) ≡
        (rawValue (R.h+1) (a+b) : Nat) [ZMOD (2^(reg R 3).length : Nat)] := by
      change (regValue R.T _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,sv,hSS]; rfl
    simpa only [vec3] using ht.step hn 3 (rawValue (R.h+1) (a+b)) r.1 r.2.2 v
  exact (((loStep.seq hiStep).seq sumStep).seq sqStep) s m init



theorem rawClearT_wires_sub (xs dst pad carry : List Wire) :
    wires (rawClearT xs dst pad carry)⊆wires (rawClear xs dst pad carry) := by
  unfold rawClearT rawClear
  exact (ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry).2.1.trans (ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry).2
theorem rawClearT_slots_le (xs dst pad carry : List Wire) :
    Challenge.gateSlots (rawClearT xs dst pad carry)≤Challenge.gateSlots (rawClear xs dst pad carry) := by
  exact (rawT_slots xs dst pad carry).2
theorem rawClearT_physical_of (xs dst pad carry : List Wire) (hm : GatePhysical (rawMake xs dst pad carry))
    (hc : GatePhysical (rawClear xs dst pad carry)) : GatePhysical (rawClearT xs dst pad carry) := by
  unfold rawClearT; exact (ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry).2.2.2 (ECDSAAdd.Entrant.TrimRow.physical xs dst pad carry hm hc).2
theorem rawClearT_counts (xs dst pad carry : List Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) :
    toffoliCount (rawClearT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=toffoliCount (rawClear xs dst pad carry) ∧
      measurementCount (rawClearT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=measurementCount (rawClear xs dst pad carry) :=
  (rawT_counts xs dst pad carry hx hd hp hc).2

theorem rawclearlo_transitionT (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (B S T : Int) :
    Transition R base (vec (rawValue R.h (regValue R.lo base.basis)) B S T) (vec 0 B S T) (rawClearT R.lo R.dlo R.pad R.carry) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have hpl := w.pad
  have hlen : R.lo.length=R.h := by omega
  have hdlen : R.dlo.length=2*R.h := by omega
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have rb := rawValue_bound R.lo base.basis (by omega)
  rw [hlen] at rb
  have dv := ht.exact 0 (rawValue R.h (regValue R.lo base.basis)) rfl
    (by change _<2^R.dlo.length; rw [hdlen]; exact rb)
  change regValue R.dlo t.basis=_ at dv
  have r := rawClearT_correct R.lo R.dlo R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 0) (run (rawClearT R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 0).length : Nat)] := by
    change (regValue R.dlo _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec0] using ht.step hn 0 0 r.1 r.2.2 val

theorem rawclearhi_transitionT (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (A S T : Int) :
    Transition R base (vec A (rawValue R.h (regValue R.hi base.basis)) S T) (vec A 0 S T) (rawClearT R.hi R.dhi R.pad R.carry) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have hpl := w.pad
  have hlen : R.hi.length=R.h := by omega
  have hdlen : R.dhi.length=2*R.h := by omega
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have rb := rawValue_bound R.hi base.basis (by omega)
  rw [hlen] at rb
  have dv := ht.exact 1 (rawValue R.h (regValue R.hi base.basis)) rfl
    (by change _<2^R.dhi.length; rw [hdlen]; exact rb)
  change regValue R.dhi t.basis=_ at dv
  have r := rawClearT_correct R.hi R.dhi R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 1) (run (rawClearT R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 1).length : Nat)] := by
    change (regValue R.dhi _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec1] using ht.step hn 1 0 r.1 r.2.2 val

theorem rawclearSum_transitionT (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hp0 : regValue R.pad base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (A B : Int) (S : Nat) (hS : S<2^R.S.length) :
    Transition R base (vec A B S (rawValue R.S.length S)) (vec A B S 0)
      (rawClearT R.S R.T R.pad R.carry) := by
  intro t rec ht
  have h4 := w.h4; have hh := w.hh; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hpl := w.pad
  have sv := ht.exact 2 S rfl hS
  change regValue R.S t.basis=S at sv
  have rb := rawValue_bound R.S t.basis (by omega)
  rw [sv] at rb
  have dv := ht.exact 3 (rawValue R.S.length S) rfl (by change _<2^R.T.length; rw [htl]; exact rb)
  change regValue R.T t.basis=_ at dv
  have r := rawClearT_correct R.S R.T R.pad R.carry
    (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by omega) htl hpl (by omega) t rec (by rw [sv]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 3) (run (rawClearT R.S R.T R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 3).length : Nat)] := by
    change (regValue R.T _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec3] using ht.step hn 3 0 r.1 r.2.2 val

end ECDSAAdd.Entrant.DiagSq

section
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-! Constant `+1` on the top three bits with a clean carry-in: the bit-0 majority of a
constant-one bit is `[CX y c, CX cin c, CCX y cin c]`, and its Toffoli is the identity
while `cin = 0`. `incr1` drops it. -/

theorem ccx_noop (a b t : Wire) (p : Program) (m : List Bool) (s : State) (h : s.basis b=false) :
    run (.CCX a b t :: p) m s=run p m s := by
  have e : (⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩ : State)=s := by
    obtain ⟨ph,bs⟩ := s
    simp only at h
    congr 1
    funext q
    by_cases hq : q=t
    · subst hq; simp [writeBit,h]
    · simp [writeBit,Function.update,hq]
  simp only [run]
  rw [e]

theorem run_cx_cx_ccx (y cin c : Wire) (X : Program) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (hcc : cin≠c) :
    run (.CX y c :: .CX cin c :: .CCX y cin c :: X) m s=run (.CX y c :: .CX cin c :: X) m s := by
  let t1 : State := ⟨s.phase,writeBit s.basis c (s.basis c ^^ s.basis y)⟩
  let t2 : State := ⟨t1.phase,writeBit t1.basis c (t1.basis c ^^ t1.basis cin)⟩
  have ht2 : t2.basis cin=false := by
    simp [t2,t1,writeBit,Function.update,hcc,hi]
  calc run (.CX y c :: .CX cin c :: .CCX y cin c :: X) m s=run (.CCX y cin c :: X) m t2 := rfl
    _=run X m t2 := ccx_noop _ _ _ _ _ _ ht2
    _=run (.CX y c :: .CX cin c :: X) m s := rfl

def incr1 (ys carry : List Wire) (cin : Wire) : Program :=
  match ys, carry with
  | y::y'::ys', c::cs => [.CX y c,.CX cin c]++mappedAdd (mappedConstant none 2 0) (y'::ys') cs c++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin
  | _, _ => mappedAdd (mappedConstant none 3 1) ys carry cin

theorem incr1_split (y y' c cin : Wire) (ys cs : List Wire) :
    mappedAdd (mappedConstant none 3 1) (y::y'::ys) (c::cs) cin=
      [.CX y c,.CX cin c,.CCX y cin c]++(mappedAdd (mappedConstant none 2 0) (y'::ys) cs c++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin) := by
  simp [mappedConstant,mappedAdd,mappedMajority,mappedConstantBit,List.append_assoc]

theorem incr1_run (ys carry : List Wire) (cin : Wire) (s : State) (m : List Bool)
    (hi : s.basis cin=false) (hc : ∀c∈carry.take 1,cin≠c) :
    run (incr1 ys carry cin) m s=run (mappedAdd (mappedConstant none 3 1) ys carry cin) m s := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try rfl
  have hcc : cin≠c := hc c (by simp)
  rw [incr1_split]
  simp only [incr1,List.append_assoc,List.cons_append,List.nil_append]
  exact (run_cx_cx_ccx y cin c _ m s hi hcc).symm

theorem incr1_mc (ys carry : List Wire) (cin : Wire) :
    measurementCount (incr1 ys carry cin)=measurementCount (mappedAdd (mappedConstant none 3 1) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> rfl

def decr1 (ys carry : List Wire) (cin : Wire) : Program :=
  notRegister ys++incr1 ys carry cin++notRegister ys

theorem decr1_run (ys carry : List Wire) (cin : Wire) (s : State) (m : List Bool)
    (hi : s.basis cin=false) (hc : ∀c∈carry.take 1,cin≠c) (hy : cin∉ys) (hyn : ys.Nodup) :
    run (decr1 ys carry cin) m s=run (mappedSub (mappedConstant none 3 1) ys carry cin) m s := by
  have hm : measurementCount (notRegister ys)=0 := (notRegister_counts ys).2
  have nr := notRegister_correct ys hyn s []
  simp only [decr1,mappedSub,List.append_assoc]
  rw [run_append (notRegister ys),run_append (notRegister ys),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (incr1 ys carry cin),run_append (mappedAdd (mappedConstant none 3 1) ys carry cin),incr1_mc,
    incr1_run ys carry cin _ _ (by rw [nr]; simp [hy,hi]) hc]

theorem incr1_mem (ys carry : List Wire) (cin : Wire) :
    ∀i∈incr1 ys carry cin,i∈mappedAdd (mappedConstant none 3 1) ys carry cin := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try (intro i h; exact h)
  rw [incr1_split]
  intro i h
  simp only [incr1,List.mem_append,List.mem_cons] at h ⊢
  tauto

theorem incr1_counts (ys carry : List Wire) (cin : Wire) (h2 : 2≤ys.length) (hc : 1≤carry.length) :
    toffoliCount (incr1 ys carry cin)+1=toffoliCount (mappedAdd (mappedConstant none 3 1) ys carry cin) ∧
    measurementCount (incr1 ys carry cin)=measurementCount (mappedAdd (mappedConstant none 3 1) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> simp at h2 hc
  rw [incr1_split]
  simp only [incr1,toffoliCount_append,measurementCount_append]
  simp [toffoliCount,measurementCount]
  omega

theorem incr1_slots (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (incr1 ys carry cin)≤Challenge.gateSlots (mappedAdd (mappedConstant none 3 1) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try exact le_refl _
  rw [incr1_split]
  simp only [incr1,Challenge.gateSlots_append]
  simp [Challenge.gateSlots,Challenge.instructionSlots]
  omega

theorem wires_of_mem {p q : Program} (h : ∀i∈p,i∈q) : wires p⊆wires q := by
  induction p with
  | nil => simp [wires]
  | cons i p ih =>
    simp only [wires]
    apply Finset.union_subset
    · intro w hw
      have hq := h i (by simp)
      clear h ih
      induction q with
      | nil => simp at hq
      | cons j q ihq =>
        simp only [wires,Finset.mem_union]
        rcases List.mem_cons.mp hq with e|e
        · subst e; exact Or.inl hw
        · exact Or.inr (ihq e)
    · exact ih (fun j hj => h j (by simp [hj]))

def correctionZ (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h ++
    incr1 (dst.drop (2*h-1)) (carry.take 2) cin

def correctionBackZ (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  decr1 (dst.drop (2*h-1)) (carry.take 2) cin ++
  loadedAdd (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h

theorem correctionZ_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)+
      (2^(2*h-1) : Nat)) s (run (correctionZ h as bs ss dst carry q cin) m s) := by
  let P := loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h
  have r := sharedSub_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s
    (m.take (measurementCount P)) hv hq0 hi0 hc0
  have out (w : Wire) (hw : w∈cin::carry) : w∉dst :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have ui : (run P (m.take (measurementCount P)) s).basis cin=false := (r.2.1 cin (out cin (by simp))).trans hi0
  have hc : ∀c∈(carry.take 2).take 1,cin≠c := by
    intro c hc e; subst e
    have := List.mem_of_mem_take (List.mem_of_mem_take hc)
    have h0 := (List.nodup_cons.mp hn).1
    exact h0 (by simp [this])
  have e : run (correctionZ h as bs ss dst carry q cin) m s=run (correction h as bs ss dst carry q cin) m s := by
    simp only [correctionZ,correction,run_append]
    exact incr1_run _ _ _ _ _ ui hc
  rw [e]
  exact correction_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s m hv hq0 hi0 hc0

theorem correctionBackZ_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)-
      (2^(2*h-1) : Nat)) s (run (correctionBackZ h as bs ss dst carry q cin) m s) := by
  have hc : ∀c∈(carry.take 2).take 1,cin≠c := by
    intro c hc e; subst e
    have := List.mem_of_mem_take (List.mem_of_mem_take hc)
    have h0 := (List.nodup_cons.mp hn).1
    exact h0 (by simp [this])
  have hy : cin∉dst.drop (2*h-1) := by
    intro hy
    have h0 := (List.nodup_cons.mp hn).1
    exact h0 (by simp [List.mem_of_mem_drop hy])
  have hyn : (dst.drop (2*h-1)).Nodup := by
    apply List.Nodup.sublist (List.drop_sublist _ _)
    exact nd_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega)
  have e : run (correctionBackZ h as bs ss dst carry q cin) m s=run (correctionBack h as bs ss dst carry q cin) m s := by
    simp only [correctionBackZ,correctionBack,run_append]
    have mc : measurementCount (decr1 (dst.drop (2*h-1)) (carry.take 2) cin)=
        measurementCount (mappedSub (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin) := by
      have a := incr1_counts (dst.drop (2*h-1)) (carry.take 2) cin
        (by simp only [List.length_drop]; rcases hh with rfl|rfl <;> omega)
        (by simp only [List.length_take]; omega)
      simp only [decr1,mappedSub,measurementCount_append,a.2]
    rw [mc,decr1_run _ _ _ _ _ hi0 hc hy hyn]
  rw [e]
  exact correctionBack_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s m hv hq0 hi0 hc0

def corrZ (R : KRegs) : Program := correctionZ R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
def corrBackZ (R : KRegs) : Program := correctionBackZ R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin

theorem corrZ_mem (R : KRegs) : ∀i∈corrZ R,i∈corr R := by
  intro i h
  simp only [corrZ,corr,correctionZ,correction,List.mem_append] at h ⊢
  rcases h with h|h
  · exact Or.inl h
  · exact Or.inr (incr1_mem _ _ _ i h)
theorem corrBackZ_mem (R : KRegs) : ∀i∈corrBackZ R,i∈corrBack R := by
  intro i h
  simp only [corrBackZ,corrBack,correctionBackZ,correctionBack,decr1,mappedSub,List.mem_append] at h ⊢
  rcases h with ((h|h)|h)|h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr (incr1_mem _ _ _ i h)))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem corrZ_counts (R : KRegs) (w : R.W) :
    toffoliCount (corrZ R)+1=toffoliCount (corr R) ∧ measurementCount (corrZ R)=measurementCount (corr R) := by
  have hTl := w.T; have hSl := w.S; have hcl := w.carry; have hh2 := w.hh; have h5 := w.h5
  have a := incr1_counts (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
    (by simp only [List.length_drop]; have h4 := w.h4; omega)
    (by simp only [List.length_take]; omega)
  simp only [corrZ,corr,correctionZ,correction,toffoliCount_append,measurementCount_append]
  omega
theorem corrBackZ_counts (R : KRegs) (w : R.W) :
    toffoliCount (corrBackZ R)+1=toffoliCount (corrBack R) ∧ measurementCount (corrBackZ R)=measurementCount (corrBack R) := by
  have hTl := w.T; have hSl := w.S; have hcl := w.carry; have hh2 := w.hh; have h5 := w.h5
  have a := incr1_counts (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
    (by simp only [List.length_drop]; have h4 := w.h4; omega)
    (by simp only [List.length_take]; omega)
  simp only [corrBackZ,corrBack,correctionBackZ,correctionBack,decr1,mappedSub,toffoliCount_append,measurementCount_append]
  omega
theorem corrZ_slots (R : KRegs) : Challenge.gateSlots (corrZ R)≤Challenge.gateSlots (corr R) := by
  have a := incr1_slots (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  simp only [corrZ,corr,correctionZ,correction,Challenge.gateSlots_append]
  omega
theorem corrBackZ_slots (R : KRegs) : Challenge.gateSlots (corrBackZ R)≤Challenge.gateSlots (corrBack R) := by
  have a := incr1_slots (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  simp only [corrBackZ,corrBack,correctionBackZ,correctionBack,decr1,mappedSub,Challenge.gateSlots_append]
  omega

theorem corrZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) (T-((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)+(2^(2*R.h-1) : Nat))) (corrZ R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hzl := w.z
  have hhi : R.hi.length=R.h := by omega
  have hs : R.S.length=R.h+1 := by omega
  have qm : parity R∈R.z := getD_in R.z 0 (by omega)
  have qsub : List.Sublist [parity R] R.z := List.singleton_sublist.mpr qm
  have cn : (R.cin::parity R::R.lo++R.hi++R.S++R.T++R.carry).Nodup := knd hn (fun q => by
    have c := R.counts q; have z := qsub.count_le q
    simp only [KRegs.all,List.count_cons,List.count_append,List.count_nil] at c z ⊢; omega)
  have av := regValue_lt R.lo base.basis
  have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hhi] at bv
  have slt : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [hs,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) slt
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have zv := (ht.keep hn R.z (by intro q h; simp [h])).trans hz0
  have r := correctionZ_correct R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    hh L0 hhi hs (by omega) (by omega) cn t rec (by rw [sv,al,bl])
    ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv
  rw [al,bl] at r
  have act := ht.advance hn 3 _ r
  convert act using 1 <;> simp only [vec3]
  congr 1
  change _=T+_
  ring

theorem corrBackZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) (T+((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)-(2^(2*R.h-1) : Nat))) (corrBackZ R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hzl := w.z
  have hhi : R.hi.length=R.h := by omega
  have hs : R.S.length=R.h+1 := by omega
  have qm : parity R∈R.z := getD_in R.z 0 (by omega)
  have qsub : List.Sublist [parity R] R.z := List.singleton_sublist.mpr qm
  have cn : (R.cin::parity R::R.lo++R.hi++R.S++R.T++R.carry).Nodup := knd hn (fun q => by
    have c := R.counts q; have z := qsub.count_le q
    simp only [KRegs.all,List.count_cons,List.count_append,List.count_nil] at c z ⊢; omega)
  have av := regValue_lt R.lo base.basis
  have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hhi] at bv
  have slt : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [hs,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) slt
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have zv := (ht.keep hn R.z (by intro q h; simp [h])).trans hz0
  have r := correctionBackZ_correct R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    hh L0 hhi hs (by omega) (by omega) cn t rec (by rw [sv,al,bl])
    ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv
  rw [al,bl] at r
  have act := ht.advance hn 3 _ r
  convert act using 1 <;> simp only [vec3]
  congr 1
  change _=T+_
  ring


end ECDSAAdd.Entrant.DiagSq
end

section
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-! Diagonal add/subtract whose lowest target bit is known. The bit-0 majority of
`mappedAdd (mappedDiagonal xs)` is `majority x₀ y₀ cin c`; with `cin = 0` its Toffoli
fires on `(y₀ ⊕ x₀) ∧ x₀`, which is zero whenever `x₀ → y₀`. For the subtraction
(complemented target) this holds when the target is even, for the addition when the
target's bit 0 equals `x₀`. `addHead0` drops that Toffoli (its carry is then just `x₀`). -/

theorem ccx_noop2 (a b t : Wire) (p : Program) (m : List Bool) (s : State)
    (h : (s.basis a && s.basis b)=false) : run (.CCX a b t :: p) m s=run p m s := by
  have e : (⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩ : State)=s := by
    obtain ⟨ph,bs⟩ := s
    simp only at h
    congr 1
    funext q
    by_cases hq : q=t
    · subst hq; simp [writeBit,h]
    · simp [writeBit,Function.update,hq]
  simp only [run]
  rw [e]

theorem run_maj_idle (a y cin c : Wire) (X : Program) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (hay : s.basis a=true → s.basis y=true)
    (h1 : a≠y) (h3 : y≠cin) :
    run (.CX a y :: .CX a cin :: .CCX y cin c :: X) m s=run (.CX a y :: .CX a cin :: X) m s := by
  let t1 : State := ⟨s.phase,writeBit s.basis y (s.basis y ^^ s.basis a)⟩
  let t2 : State := ⟨t1.phase,writeBit t1.basis cin (t1.basis cin ^^ t1.basis a)⟩
  have ht2 : (t2.basis y && t2.basis cin)=false := by
    have e1 : t2.basis y=(s.basis y ^^ s.basis a) := by
      simp [t2,t1,writeBit,Function.update,h3]
    have e2 : t2.basis cin=s.basis a := by
      simp [t2,t1,writeBit,Function.update,h3.symm,h1,hi]
    rw [e1,e2]
    cases ha : s.basis a <;> cases hy : s.basis y <;> simp_all
  calc run (.CX a y :: .CX a cin :: .CCX y cin c :: X) m s=run (.CCX y cin c :: X) m t2 := rfl
    _=run X m t2 := ccx_noop2 _ _ _ _ _ _ ht2
    _=run (.CX a y :: .CX a cin :: X) m s := rfl

def maj0 (a y cin c : Wire) : Program := [.CX a y,.CX a cin,.CX a c,.CX a cin,.CX a y]

def addHead0 (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
  match bits, ys, carry with
  | ⟨some a,false⟩::b'::bits', y::y'::ys', c::cs =>
      maj0 a y cin c++(mappedAdd (b'::bits') (y'::ys') cs c++
        mappedEraseCarry ⟨some a,false⟩ y cin c++mappedSum ⟨some a,false⟩ y cin)
  | bits, ys, carry => mappedAdd bits ys carry cin

theorem addHead0_split (a y y' c cin : Wire) (b' : MappedBit) (bits : List MappedBit) (ys cs : List Wire) :
    mappedAdd (⟨some a,false⟩::b'::bits) (y::y'::ys) (c::cs) cin=
      majority a y cin c++(mappedAdd (b'::bits) (y'::ys) cs c++
        mappedEraseCarry ⟨some a,false⟩ y cin c++mappedSum ⟨some a,false⟩ y cin) := by
  simp [mappedAdd,mappedMajority,List.append_assoc]

theorem addHead0_run (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (hay : ∀y ys',ys=y::ys' → s.basis a=true → s.basis y=true)
    (h1 : a∉ys) (h3 : cin∉ys) :
    run (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin) m s=
      run (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) m s := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try rfl
  rw [addHead0_split]
  simp only [addHead0,maj0,majority,List.cons_append,List.nil_append]
  exact (run_maj_idle a y cin c _ m s hi (hay y _ rfl) (fun e => h1 (by simp [e]))
    (fun e => h3 (by simp [e]))).symm

theorem addHead0_mem (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    ∀i∈addHead0 (⟨some a,false⟩::b'::bits) ys carry cin,i∈mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try (intro i h; exact h)
  rw [addHead0_split]
  intro i h
  simp only [addHead0,maj0,majority,List.mem_append,List.mem_cons] at h ⊢
  tauto

theorem addHead0_mc (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    measurementCount (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)=
      measurementCount (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> rfl

theorem addHead0_counts (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (h2 : 2≤ys.length) (hc : 1≤carry.length) :
    toffoliCount (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)+1=
      toffoliCount (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) ∧
    measurementCount (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)=
      measurementCount (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> simp at h2 hc
  rw [addHead0_split]
  simp only [addHead0,maj0,majority,toffoliCount_append,measurementCount_append]
  simp [toffoliCount,measurementCount]
  omega

theorem addHead0_slots (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)≤
      Challenge.gateSlots (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try exact le_refl _
  rw [addHead0_split]
  simp only [addHead0,maj0,majority,Challenge.gateSlots_append]
  simp [Challenge.gateSlots,Challenge.instructionSlots]

theorem diag_cons (x : Wire) (xs : List Wire) :
    ∃ b' bits,mappedDiagonal (x::xs)=⟨some x,false⟩::b'::bits := by
  cases xs with
  | nil => exact ⟨_,_,rfl⟩
  | cons x' xs => exact ⟨_,_,rfl⟩

def dAddZ (xs dst carry : List Wire) (cin : Wire) : Program :=
  addHead0 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin

def dSubZ (xs dst carry : List Wire) (cin : Wire) : Program :=
  notRegister dst++dAddZ xs dst carry cin++notRegister dst

theorem dAddZ_mem (xs dst carry : List Wire) (cin : Wire) :
    ∀i∈dAddZ xs dst carry cin,i∈mappedDiagAdd xs dst carry cin := by
  rcases xs with _|⟨x,xs⟩
  · intro i h; exact h
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    exact addHead0_mem _ _ _ _ _ _

theorem dSubZ_mem (xs dst carry : List Wire) (cin : Wire) :
    ∀i∈dSubZ xs dst carry cin,i∈mappedDiagSub xs dst carry cin := by
  intro i h
  simp only [dSubZ,mappedDiagSub,mappedSub,List.mem_append] at h ⊢
  rcases h with (h|h)|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (dAddZ_mem xs dst carry cin i h))
  · exact Or.inr h

theorem dAddZ_counts (xs dst carry : List Wire) (cin : Wire) (hx : 0<xs.length)
    (hd : 2≤dst.length) (hc : 1≤carry.length) :
    toffoliCount (dAddZ xs dst carry cin)+1=toffoliCount (mappedDiagAdd xs dst carry cin) ∧
    measurementCount (dAddZ xs dst carry cin)=measurementCount (mappedDiagAdd xs dst carry cin) := by
  rcases xs with _|⟨x,xs⟩
  · simp at hx
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    exact addHead0_counts _ _ _ _ _ _ hd (by simp only [List.length_take]; omega)

theorem dSubZ_counts (xs dst carry : List Wire) (cin : Wire) (hx : 0<xs.length)
    (hd : 2≤dst.length) (hc : 1≤carry.length) :
    toffoliCount (dSubZ xs dst carry cin)+1=toffoliCount (mappedDiagSub xs dst carry cin) ∧
    measurementCount (dSubZ xs dst carry cin)=measurementCount (mappedDiagSub xs dst carry cin) := by
  have a := dAddZ_counts xs dst carry cin hx hd hc
  simp only [dAddZ,mappedDiagAdd] at a
  simp only [dSubZ,dAddZ,mappedDiagSub,mappedSub,toffoliCount_append,measurementCount_append]
  omega

theorem dAddZ_slots (xs dst carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (dAddZ xs dst carry cin)≤Challenge.gateSlots (mappedDiagAdd xs dst carry cin) := by
  rcases xs with _|⟨x,xs⟩
  · exact le_refl _
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    exact addHead0_slots _ _ _ _ _ _

theorem dSubZ_slots (xs dst carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (dSubZ xs dst carry cin)≤Challenge.gateSlots (mappedDiagSub xs dst carry cin) := by
  have a := dAddZ_slots xs dst carry cin
  simp only [dAddZ,mappedDiagAdd] at a
  simp only [dSubZ,dAddZ,mappedDiagSub,mappedSub,Challenge.gateSlots_append]
  omega

theorem dAddZ_run (xs dst carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin::xs++dst++carry).Nodup) (hi : s.basis cin=false)
    (hay : ∀y ys',dst=y::ys' → s.basis (xs.headD 0)=true → s.basis y=true) :
    run (dAddZ xs dst carry cin) m s=run (mappedDiagAdd xs dst carry cin) m s := by
  rcases xs with _|⟨x,xs⟩
  · rfl
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    have hx : x∉dst := dis_count (r:=x::xs) (t:=dst) hn (fun w => by simp only [List.count_cons,List.count_append]; omega) x (by simp)
    have hc : cin∉dst := dis_count (r:=[cin]) (t:=dst) hn (fun w => by simp only [List.count_cons,List.count_append,List.count_nil]; omega) cin (by simp)
    exact addHead0_run x b' bits dst _ cin m s hi (by simpa using hay) hx hc

theorem dSubZ_run (xs dst carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin::xs++dst++carry).Nodup) (hi : s.basis cin=false)
    (hy : s.basis (dst.headD 0)=false) :
    run (dSubZ xs dst carry cin) m s=run (mappedDiagSub xs dst carry cin) m s := by
  have hm : measurementCount (notRegister dst)=0 := (notRegister_counts dst).2
  have hdn : dst.Nodup := nd_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega)
  have nr := notRegister_correct dst hdn s []
  have hc : cin∉dst := dis_count (r:=[cin]) (t:=dst) hn (fun w => by simp only [List.count_cons,List.count_append,List.count_nil]; omega) cin (by simp)
  have mc : measurementCount (dAddZ xs dst carry cin)=measurementCount (mappedAdd (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin) := by
    rcases xs with _|⟨x,xs⟩
    · rfl
    · obtain ⟨b',bits,e⟩ := diag_cons x xs
      simp only [dAddZ,e]
      exact addHead0_mc _ _ _ _ _ _
  simp only [dSubZ,mappedDiagSub,mappedSub,List.append_assoc]
  rw [run_append (notRegister dst),run_append (notRegister dst),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (dAddZ xs dst carry cin),run_append (mappedAdd (mappedDiagonal xs) dst _ cin),mc]
  have e := dAddZ_run xs dst carry cin (m.take (measurementCount (mappedAdd (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin)))
    (run (notRegister dst) [] s) hn (by rw [nr]; simp [hc,hi]) (by
      intro y ys' e _
      subst e
      rw [nr]
      simp at hy ⊢; simp [hy])
  simp only [dAddZ,mappedDiagAdd] at e
  simp only [dAddZ]
  rw [e]

end ECDSAAdd.Entrant.DiagSq
end

section
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic

/-! Bit 1 of a square is always zero (`b² mod 4 ∈ {0,1}`). In `m7g : T −= b²` and
`c7g : T += b²` the bit-0 carry is already dropped (its carry-in for bit 1 is the clean
`cin`), so the bit-1 majority has source bit `0` and carry-in `0`: its Toffoli is idle.
`addHeadI` drops the Toffoli of the first majority of an in-place adder whose first
source bit is zero. -/

def addHeadI : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as, b::b'::bs, c::cs, cin =>
      DiagSq.maj0 a b cin c++(addInPlace (a'::as) (b'::bs) cs c++eraseCarry a b cin c++[.CX a b,.CX cin b])
  | x, y, c, cin => addInPlace x y c cin

theorem addHeadI_split (a a' b b' c cin : Wire) (as bs cs : List Wire) :
    addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin=
      majority a b cin c++(addInPlace (a'::as) (b'::bs) cs c++eraseCarry a b cin c++[.CX a b,.CX cin b]) := by
  simp [addInPlace,List.append_assoc]

theorem addHeadI_run (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (h0 : ∀a as,x=a::as → s.basis a=false)
    (hd : ∀a as b bs,x=a::as → y=b::bs → a≠b ∧ a≠cin ∧ b≠cin) :
    run (addHeadI x y carry cin) m s=run (addInPlace x y carry cin) m s := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try rfl
  rw [addHeadI_split]
  obtain ⟨h1,-,h3⟩ := hd a _ b _ rfl rfl
  simp only [addHeadI,DiagSq.maj0,majority,List.cons_append,List.nil_append]
  exact (DiagSq.run_maj_idle a b cin c _ m s hi (by intro h; rw [h0 a _ rfl] at h; cases h) h1 h3).symm

theorem addHeadI_mem (x y carry : List Wire) (cin : Wire) :
    ∀i∈addHeadI x y carry cin,i∈addInPlace x y carry cin := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;>
    try (intro i h; exact h)
  rw [addHeadI_split]
  intro i h
  simp only [addHeadI,DiagSq.maj0,majority,List.mem_append,List.mem_cons] at h ⊢
  tauto

theorem addHeadI_counts (x y carry : List Wire) (cin : Wire) (hx : 2≤x.length) (hy : 2≤y.length)
    (hc : 1≤carry.length) :
    toffoliCount (addHeadI x y carry cin)+1=toffoliCount (addInPlace x y carry cin) ∧
    measurementCount (addHeadI x y carry cin)=measurementCount (addInPlace x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;>
    simp at hx hy hc
  rw [addHeadI_split]
  simp only [addHeadI,DiagSq.maj0,majority,toffoliCount_append,measurementCount_append]
  simp [toffoliCount,measurementCount]
  omega

theorem addHeadI_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addHeadI x y carry cin)≤Challenge.gateSlots (addInPlace x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;>
    try exact le_refl _
  rw [addHeadI_split]
  simp only [addHeadI,DiagSq.maj0,majority,Challenge.gateSlots_append]
  simp [Challenge.gateSlots,Challenge.instructionSlots]

theorem addHeadI_mc (x y carry : List Wire) (cin : Wire) :
    measurementCount (addHeadI x y carry cin)=measurementCount (addInPlace x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> rfl

/-- `addLowNC` with the bit-1 Toffoli also dropped. -/
def addLowNC1 (x y carry : List Wire) (cin : Wire) : Program :=
  addHeadI x.tail y.tail carry.tail cin ++ [.measureX (carry.headD 0) [] []] ++
    [.CX (x.headD 0) (y.headD 0), .CX cin (y.headD 0)]

def subLowNC1 (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addLowNC1 x y carry cin ++ notRegister y

theorem addLowNC1_mc (x y carry : List Wire) (cin : Wire) :
    measurementCount (addLowNC1 x y carry cin)=measurementCount (LowZero.addLowNC x y carry cin) := by
  simp only [addLowNC1,LowZero.addLowNC,measurementCount_append,addHeadI_mc]

theorem addLowNC1_run (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hi : s.basis cin=false)
    (h1 : s.basis (x.tail.headD 0)=false) :
    run (addLowNC1 x y carry cin) m s=run (LowZero.addLowNC x y carry cin) m s := by
  have hd : ∀a as b bs,x.tail=a::as → y.tail=b::bs → a≠b ∧ a≠cin ∧ b≠cin := by
    intro a as b bs ha hb
    have ax : a∈x := List.mem_of_mem_tail (by rw [ha]; simp)
    have bx : b∈y := List.mem_of_mem_tail (by rw [hb]; simp)
    have hc := (List.nodup_cons.mp hn).1
    refine ⟨fun e => ?_,fun e => hc (by rw [← e]; simp [ax]),fun e => hc (by rw [← e]; simp [bx])⟩
    rw [e] at ax
    exact DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) b ax bx
  have h0 : ∀a as,x.tail=a::as → s.basis a=false := by
    intro a as h; have := h1; rw [h] at this; simpa using this
  have e := addHeadI_run x.tail y.tail carry.tail cin
    (m.take (measurementCount (addInPlace x.tail y.tail carry.tail cin))) s hi h0 hd
  simp only [addLowNC1,LowZero.addLowNC,List.append_assoc]
  rw [run_append (addHeadI _ _ _ _),run_append (addInPlace _ _ _ _),addHeadI_mc,e]

theorem subLowNC1_run (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hi : s.basis cin=false)
    (h1 : s.basis (x.tail.headD 0)=false) (hx : 2≤x.length) :
    run (subLowNC1 x y carry cin) m s=run (LowZero.subLowNC x y carry cin) m s := by
  have hm : measurementCount (notRegister y)=0 := (notRegister_counts y).2
  have hyn : y.Nodup := DiagSq.nd_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have nr := notRegister_correct y hyn s []
  have hc : cin∉y := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hx1 : x.tail.headD 0∈x := by rcases x with _|⟨a,_|⟨b,xs⟩⟩ <;> simp at hx ⊢
  have hx2 : x.tail.headD 0∉y :=
    DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) _ hx1
  simp only [subLowNC1,LowZero.subLowNC,List.append_assoc]
  rw [run_append (notRegister y),run_append (notRegister y),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (addLowNC1 x y carry cin),
    run_append (LowZero.addLowNC x y carry cin),addLowNC1_mc,
    addLowNC1_run x y carry cin _ _ hn (by rw [nr]; simp [hc,hi]) (by rw [nr]; dsimp only; rw [if_neg hx2]; exact h1)]

theorem addLowNC1_mem (x y carry : List Wire) (cin : Wire) :
    ∀i∈addLowNC1 x y carry cin,i∈LowZero.addLowNC x y carry cin := by
  intro i h
  simp only [addLowNC1,LowZero.addLowNC,List.mem_append] at h ⊢
  rcases h with (h|h)|h
  · exact Or.inl (Or.inl (addHeadI_mem _ _ _ _ i h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem subLowNC1_mem (x y carry : List Wire) (cin : Wire) :
    ∀i∈subLowNC1 x y carry cin,i∈LowZero.subLowNC x y carry cin := by
  intro i h
  simp only [subLowNC1,LowZero.subLowNC,List.mem_append] at h ⊢
  rcases h with (h|h)|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (addLowNC1_mem _ _ _ _ i h))
  · exact Or.inr h

theorem addLowNC1_counts (x y carry : List Wire) (cin : Wire) (hx : 3≤x.length) (hy : 3≤y.length)
    (hc : 2≤carry.length) :
    toffoliCount (addLowNC1 x y carry cin)+1=toffoliCount (LowZero.addLowNC x y carry cin) := by
  have a := addHeadI_counts x.tail y.tail carry.tail cin (by simp; omega) (by simp; omega) (by simp; omega)
  simp only [addLowNC1,LowZero.addLowNC,toffoliCount_append]
  omega

theorem subLowNC1_counts (x y carry : List Wire) (cin : Wire) (hx : 3≤x.length) (hy : 3≤y.length)
    (hc : 2≤carry.length) :
    toffoliCount (subLowNC1 x y carry cin)+1=toffoliCount (LowZero.subLowNC x y carry cin) := by
  have a := addLowNC1_counts x y carry cin hx hy hc
  simp only [subLowNC1,LowZero.subLowNC,toffoliCount_append]
  omega

theorem addLowNC1_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addLowNC1 x y carry cin)≤Challenge.gateSlots (LowZero.addLowNC x y carry cin) := by
  have a := addHeadI_slots x.tail y.tail carry.tail cin
  simp only [addLowNC1,LowZero.addLowNC,Challenge.gateSlots_append]
  omega

theorem subLowNC1_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (subLowNC1 x y carry cin)≤Challenge.gateSlots (LowZero.subLowNC x y carry cin) := by
  have a := addLowNC1_slots x y carry cin
  simp only [subLowNC1,LowZero.subLowNC,Challenge.gateSlots_append]
  omega

theorem bit1 (r tail : List Wire) (st : BasisState) (hl : 2≤r.length) :
    st ((r++tail).tail.headD 0)=decide (regValue r st/2%2=1) := by
  match r, hl with
  | w::ws, hl2 =>
    have hne : ws≠[] := by intro e; subst e; simp at hl2
    simp only [List.cons_append,List.tail_cons]
    rw [LowZero.head_bit ws tail st hne,LowZero.foldr_cons_value]
    have : ((if st w then 1 else 0)+2*regValue ws st)/2=regValue ws st := by split <;> omega
    rw [this]

theorem sq_bit1 (b : Nat) : b^2/2%2=0 := by
  have h : b^2%4=0 ∨ b^2%4=1 := by
    rw [Nat.pow_mod]
    have : b%4<4 := Nat.mod_lt _ (by norm_num)
    interval_cases (b%4) <;> simp
  omega

variable (R : KRegs)

theorem dhi_two (w : R.W) : 2≤R.dhi.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  omega

def m7y : Program :=
  if (R.dhi++R.zB).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length then
    subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin else R.m7g
def c7y : Program :=
  if (R.dhi++R.zB).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length then
    addLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin else R.c7g

theorem m7y_mem : ∀i∈R.m7y,i∈R.m7g := by
  unfold m7y
  split_ifs with h
  · unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact subLowNC1_mem _ _ _ _
  · exact fun i hi => hi
theorem c7y_mem : ∀i∈R.c7y,i∈R.c7g := by
  unfold c7y
  split_ifs with h
  · unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact addLowNC1_mem _ _ _ _
  · exact fun i hi => hi

theorem m7y_wires : wires R.m7y⊆wires R.m7 := (DiagSq.wires_of_mem R.m7y_mem).trans R.m7g_wires
theorem c7y_wires : wires R.c7y⊆wires R.c7 := (DiagSq.wires_of_mem R.c7y_mem).trans R.c7g_wires
theorem m7y_physical (hn : R.all.Nodup) : GatePhysical R.m7y := fun i hi => R.m7g_physical hn i (R.m7y_mem i hi)
theorem c7y_physical (hn : R.all.Nodup) : GatePhysical R.c7y := fun i hi => R.c7g_physical hn i (R.c7y_mem i hi)

theorem m7y_slots : Challenge.gateSlots R.m7y≤Challenge.gateSlots R.m7 := by
  refine le_trans ?_ R.m7g_slots
  unfold m7y
  split_ifs with h
  · unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact subLowNC1_slots _ _ _ _
  · exact le_refl _
theorem c7y_slots : Challenge.gateSlots R.c7y≤Challenge.gateSlots R.c7 := by
  refine le_trans ?_ R.c7g_slots
  unfold c7y
  split_ifs with h
  · unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact addLowNC1_slots _ _ _ _
  · exact le_refl _

theorem m7y_counts (w : R.W) : toffoliCount R.m7y+2=toffoliCount R.m7 ∧
    measurementCount R.m7y=measurementCount R.m7 := by
  have l := R.t_lensg w
  have z := R.m7g_counts w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have c := subLowNC1_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by rw [l.1]; omega) (by omega) (by simp only [List.length_take]; omega)
  have mc : measurementCount R.m7y=measurementCount R.m7g := by
    unfold m7y m7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    simp only [subLowNC1,LowZero.subLowNC,measurementCount_append,addLowNC1_mc]
  have tc : toffoliCount R.m7y+1=toffoliCount R.m7g := by
    unfold m7y m7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]; exact c
  constructor <;> omega
theorem c7y_counts (w : R.W) : toffoliCount R.c7y+2=toffoliCount R.c7 ∧
    measurementCount R.c7y=measurementCount R.c7 := by
  have l := R.t_lensg w
  have z := R.c7g_counts w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have c := addLowNC1_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by rw [l.1]; omega) (by omega) (by simp only [List.length_take]; omega)
  have mc : measurementCount R.c7y=measurementCount R.c7g := by
    unfold c7y c7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    exact addLowNC1_mc _ _ _ _
  have tc : toffoliCount R.c7y+1=toffoliCount R.c7g := by
    unfold c7y c7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]; exact c
  constructor <;> omega

theorem m7y_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false) :
    (run R.m7y m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7y m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7y m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  have e : run R.m7y m s=run R.m7g m s := by
    unfold m7y m7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    exact subLowNC1_run _ _ _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) hi h1 (by rw [l.1]; exact l.2.2.1)
  rw [e]; exact R.m7g_correct w hn s m hcl hnc hi
theorem c7y_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false) :
    (run R.c7y m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7y m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7y m s).basis=(regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  have e : run R.c7y m s=run R.c7g m s := by
    unfold c7y c7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    exact addLowNC1_run _ _ _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) hi h1
  rw [e]; exact R.c7g_correct w hn s m hcl hnc hi

end ECDSAAdd.Entrant.KRegs
end

section
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic

/-! Inner `T −= A` / `T += A` with a bounded low part. In every inner leaf the subtracted
value `A = rawValue h a < 2^{2h}` never exceeds the low `2h+1` bits of `T = rawValue (h+1) S`,
so the borrow out of bit `2h` is always zero and the 66/68-bit adder can run on the low
`2h+1` bits only (one majority/erase pair fewer). -/

theorem add_take_sublist (n : Nat) : ∀ (x y c : List Wire) (cin : Wire), x.length=n+2 → y.length=n+2 →
    c.length=n+1 →
    (addInPlace (x.take (n+1)) (y.take (n+1)) (c.take n) cin).Sublist (addInPlace x y c cin) := by
  induction n with
  | zero =>
    intro x y c cin hx hy hc
    match x, y, c, hx, hy, hc with
    | [a,a'], [b,b'], [c0], _, _, _ =>
      simp only [List.take, addInPlace]
      exact List.sublist_append_right _ _
  | succ n ih =>
    intro x y c cin hx hy hc
    match x, y, c, hx, hy, hc with
    | a::a'::x', b::b'::y', c0::c', hx, hy, hc =>
      have hx' : (a'::x').length=n+2 := by simpa using hx
      have hy' : (b'::y').length=n+2 := by simpa using hy
      have hc' : c'.length=n+1 := by simpa using hc
      have r := ih (a'::x') (b'::y') c' c0 hx' hy' hc'
      simp only [List.take_succ_cons] at r ⊢
      simp only [addInPlace]
      exact ((((List.Sublist.refl _).append r).append (List.Sublist.refl _)).append (List.Sublist.refl _))

theorem slots_sublist {p q : Program} (h : p.Sublist q) : Challenge.gateSlots p≤Challenge.gateSlots q := by
  unfold Challenge.gateSlots
  exact (h.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem notRegister_take_sublist (y : List Wire) (k : Nat) : (notRegister (y.take k)).Sublist (notRegister y) := by
  unfold notRegister
  rw [List.map_take]
  exact List.take_sublist _ _

/-- `addLowNC` on the low `k+2` bits is a sublist of `addLowNC` on all bits. -/
theorem addLowNC_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+3) (hy : y.length=n+3)
    (hc : c.length=n+2) :
    (LowZero.addLowNC (x.take (n+2)) (y.take (n+2)) (c.take (n+1)) cin).Sublist (LowZero.addLowNC x y c cin) := by
  match x, y, c, hx, hy, hc with
  | a::x', b::y', c0::c', hx, hy, hc =>
    have r := add_take_sublist n x' y' c' cin (by simpa using hx) (by simpa using hy) (by simpa using hc)
    simp only [LowZero.addLowNC,List.take_succ_cons,List.tail_cons,List.headD_cons]
    exact (r.append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem subLowNC_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+3) (hy : y.length=n+3)
    (hc : c.length=n+2) :
    (LowZero.subLowNC (x.take (n+2)) (y.take (n+2)) (c.take (n+1)) cin).Sublist (LowZero.subLowNC x y c cin) := by
  simp only [LowZero.subLowNC]
  exact ((notRegister_take_sublist y (n+2)).append (addLowNC_take_sublist n x y c cin hx hy hc)).append
    (notRegister_take_sublist y (n+2))

variable (R : KRegs)

def lowOK : Prop := (R.dlo++R.zA).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 3≤R.T.length

instance : Decidable R.lowOK := by unfold lowOK; infer_instance

def m6w : Program := if R.lowOK then
  LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.m6z
def c6w : Program := if R.lowOK then
  LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.c6z

theorem lowOK_of (w : R.W) : R.lowOK := by
  have l := R.lo_lens w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  exact ⟨l.1,l.2.1,by omega⟩

theorem m6w_sub : R.m6w.Sublist R.m6z := by
  unfold m6w
  split_ifs with h
  · obtain ⟨h1,h2,h3⟩ := h
    unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ h1 h2 (by omega)]
    have e1 : R.T.length-1=(R.T.length-3)+2 := by omega
    have e2 : R.T.length-2=(R.T.length-3)+1 := by omega
    rw [e1,e2]
    exact subLowNC_take_sublist _ _ _ _ _ (by omega) (by omega)
      (by rw [List.length_take]; simp only [List.length_take] at h2; omega)
  · exact List.Sublist.refl _
theorem c6w_sub : R.c6w.Sublist R.c6z := by
  unfold c6w
  split_ifs with h
  · obtain ⟨h1,h2,h3⟩ := h
    unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ h1 h2 (by omega)]
    have e1 : R.T.length-1=(R.T.length-3)+2 := by omega
    have e2 : R.T.length-2=(R.T.length-3)+1 := by omega
    rw [e1,e2]
    exact addLowNC_take_sublist _ _ _ _ _ (by omega) (by omega)
      (by rw [List.length_take]; simp only [List.length_take] at h2; omega)
  · exact List.Sublist.refl _

theorem m6w_wires : wires R.m6w⊆wires R.m6 :=
  (DiagSq.wires_of_mem (fun _ h => (R.m6w_sub).subset h)).trans R.m6z_wires
theorem c6w_wires : wires R.c6w⊆wires R.c6 :=
  (DiagSq.wires_of_mem (fun _ h => (R.c6w_sub).subset h)).trans R.c6z_wires
theorem m6w_slots : Challenge.gateSlots R.m6w≤Challenge.gateSlots R.m6 :=
  (slots_sublist R.m6w_sub).trans R.m6z_slots
theorem c6w_slots : Challenge.gateSlots R.c6w≤Challenge.gateSlots R.c6 :=
  (slots_sublist R.c6w_sub).trans R.c6z_slots
theorem m6w_physical (hn : R.all.Nodup) : GatePhysical R.m6w :=
  fun i h => R.m6z_physical hn i ((R.m6w_sub).subset h)
theorem c6w_physical (hn : R.all.Nodup) : GatePhysical R.c6w :=
  fun i h => R.c6z_physical hn i ((R.c6w_sub).subset h)

theorem m6w_counts (w : R.W) : toffoliCount R.m6w+2=toffoliCount R.m6 ∧
    measurementCount R.m6w+1=measurementCount R.m6 := by
  have z := R.m6z_counts w
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have a := LowZero.subLowNC_counts _ _ _ R.cin lx lc (by simp only [List.length_take]; omega)
  have b := subInPlace_counts ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin lx lc
  have c := LowZero.subLowNC_counts _ _ _ R.cin h1 h2 (by omega)
  have d := subInPlace_counts (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin h1 h2
  have em : R.m6w=LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have ez : R.m6z=LowZero.subLowNC (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin := by
    unfold m6z; exact LowZero.subLowNCG_eq _ _ _ _ h1 h2 (by omega)
  rw [em]; rw [ez] at z
  simp only [List.length_take] at a b
  constructor <;> omega

theorem c6w_counts (w : R.W) : toffoliCount R.c6w+2=toffoliCount R.c6 ∧
    measurementCount R.c6w+1=measurementCount R.c6 := by
  have z := R.c6z_counts w
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have a := LowZero.addLowNC_counts _ _ _ R.cin lx lc (by simp only [List.length_take]; omega)
  have b := addInPlace_counts ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin lx lc
  have c := LowZero.addLowNC_counts _ _ _ R.cin h1 h2 (by omega)
  have d := addInPlace_counts (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin h1 h2
  have em : R.c6w=LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have ez : R.c6z=LowZero.addLowNC (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin := by
    unfold c6z; exact LowZero.addLowNCG_eq _ _ _ _ h1 h2 (by omega)
  rw [em]; rw [ez] at z
  simp only [List.length_take] at a b
  constructor <;> omega

theorem take_headD (l : List Wire) (k : Nat) (hk : 1≤k) : (l.take k).headD 0=l.headD 0 := by
  rcases l with _|⟨a,l⟩
  · simp
  · obtain ⟨j,rfl⟩ : ∃j,k=j+1 := ⟨k-1,by omega⟩
    simp

theorem low_nodup (hn : R.all.Nodup) :
    (R.cin::(((R.dlo++R.zA).take (R.T.length-1))++(R.T.take (R.T.length-1))++
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)))).Nodup := by
  have full : (R.cin::((R.dlo++R.zA)++R.T++(R.carry.take (R.T.length-1)))).Nodup :=
    knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  exact full.sublist ((((List.take_sublist _ _).append (List.take_sublist _ _)).append
    (List.take_sublist _ _)).cons₂ _)

theorem m6w_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (hA : regValue (R.dlo++R.zA) s.basis<2^(R.T.length-1))
    (hb : regValue (R.dlo++R.zA) s.basis≤regValue R.T s.basis%2^(R.T.length-1)) :
    (run R.m6w m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m6w m s).basis q=s.basis q) ∧
    regValue R.T (run R.m6w m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dlo++R.zA) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have em : R.m6w=LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have hTn : R.T.Nodup := knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have r := LowZero.subLowNC_correct _ _ _ R.cin (R.low_nodup hn) lx lc (by simp only [List.length_take]; omega) s m
    (fun q h => hcl q (List.mem_of_mem_take h))
    (by rw [take_headD _ _ (by omega),take_headD _ _ (by omega)]; exact hnc) hi
  rw [em]
  refine ⟨r.1,fun q h => r.2.1 q (fun h' => h (List.mem_of_mem_take h')),?_⟩
  set t := run (LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) m s with ht
  set P := 2^(R.T.length-1) with hP
  have h2P : 2^R.T.length=2*P := by rw [hP,← pow_succ']; congr 1; omega
  have xv : regValue ((R.dlo++R.zA).take (R.T.length-1)) s.basis=regValue (R.dlo++R.zA) s.basis := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega),Nat.mod_eq_of_lt hA]
  have yv : regValue (R.T.take (R.T.length-1)) s.basis=regValue R.T s.basis%P :=
    CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega) _
  have dkeep : regValue (R.T.drop (R.T.length-1)) t.basis=regValue (R.T.drop (R.T.length-1)) s.basis := by
    apply regValue_congr
    intro q hq
    apply r.2.1
    intro hq'
    have := List.disjoint_take_drop hTn (le_refl (R.T.length-1)) hq' hq
    exact this
  have split (st : BasisState) : regValue R.T st=regValue (R.T.take (R.T.length-1)) st+
      P*regValue (R.T.drop (R.T.length-1)) st := by
    have e := regValue_append (R.T.take (R.T.length-1)) (R.T.drop (R.T.length-1)) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at e
    exact e
  have dv : regValue (R.T.drop (R.T.length-1)) s.basis=regValue R.T s.basis/P :=
    CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega) _
  have tlt : regValue R.T s.basis<2*P := by rw [← h2P]; exact regValue_lt _ _
  have md := Nat.mod_add_div (regValue R.T s.basis) P
  have Ppos : 0<P := by rw [hP]; positivity
  have lowv : regValue (R.T.take (R.T.length-1)) t.basis=regValue R.T s.basis%P-regValue (R.dlo++R.zA) s.basis := by
    rw [r.2.2,xv,yv,hi,Bool.toNat_false,Nat.sub_zero,List.length_take,Nat.min_eq_left (by omega),← hP]
    rw [show regValue R.T s.basis%P+P-regValue (R.dlo++R.zA) s.basis=
      (regValue R.T s.basis%P-regValue (R.dlo++R.zA) s.basis)+P by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (by have := Nat.mod_lt (regValue R.T s.basis) Ppos; omega)]
  rw [split t.basis,lowv,dkeep,dv,hi,Bool.toNat_false,Nat.sub_zero,h2P]
  have mle := Nat.mod_le (regValue R.T s.basis) P
  generalize regValue R.T s.basis%P=M at *
  generalize regValue R.T s.basis/P=D at *
  generalize regValue R.T s.basis=TV at *
  generalize regValue (R.dlo++R.zA) s.basis=AV at *
  have dq : P*D=TV-M := by omega
  rw [dq,show TV+2*P-AV=(TV-AV)+2*P by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  omega

theorem c6w_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (hA : regValue (R.dlo++R.zA) s.basis<2^(R.T.length-1))
    (hb : regValue R.T s.basis%2^(R.T.length-1)+regValue (R.dlo++R.zA) s.basis<2^(R.T.length-1)) :
    (run R.c6w m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c6w m s).basis q=s.basis q) ∧
    regValue R.T (run R.c6w m s).basis=(regValue (R.dlo++R.zA) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have em : R.c6w=LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have hTn : R.T.Nodup := knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have r := LowZero.addLowNC_correct _ _ _ R.cin (R.low_nodup hn) lx lc (by simp only [List.length_take]; omega) s m
    (fun q h => hcl q (List.mem_of_mem_take h))
    (by rw [take_headD _ _ (by omega),take_headD _ _ (by omega)]; exact hnc) hi
  rw [em]
  refine ⟨r.1,fun q h => r.2.1 q (fun h' => h (List.mem_of_mem_take h')),?_⟩
  set t := run (LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) m s with ht
  set P := 2^(R.T.length-1) with hP
  have h2P : 2^R.T.length=2*P := by rw [hP,← pow_succ']; congr 1; omega
  have xv : regValue ((R.dlo++R.zA).take (R.T.length-1)) s.basis=regValue (R.dlo++R.zA) s.basis := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega),Nat.mod_eq_of_lt hA]
  have yv : regValue (R.T.take (R.T.length-1)) s.basis=regValue R.T s.basis%P :=
    CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega) _
  have dkeep : regValue (R.T.drop (R.T.length-1)) t.basis=regValue (R.T.drop (R.T.length-1)) s.basis := by
    apply regValue_congr
    intro q hq
    apply r.2.1
    intro hq'
    exact List.disjoint_take_drop hTn (le_refl (R.T.length-1)) hq' hq
  have split (st : BasisState) : regValue R.T st=regValue (R.T.take (R.T.length-1)) st+
      P*regValue (R.T.drop (R.T.length-1)) st := by
    have e := regValue_append (R.T.take (R.T.length-1)) (R.T.drop (R.T.length-1)) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at e
    exact e
  have dv : regValue (R.T.drop (R.T.length-1)) s.basis=regValue R.T s.basis/P :=
    CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega) _
  have tlt : regValue R.T s.basis<2*P := by rw [← h2P]; exact regValue_lt _ _
  have md := Nat.mod_add_div (regValue R.T s.basis) P
  have Ppos : 0<P := by rw [hP]; positivity
  have lowv : regValue (R.T.take (R.T.length-1)) t.basis=regValue (R.dlo++R.zA) s.basis+regValue R.T s.basis%P := by
    rw [r.2.2,xv,yv,hi,Bool.toNat_false,Nat.add_zero,List.length_take,Nat.min_eq_left (by omega),← hP]
    exact Nat.mod_eq_of_lt (by omega)
  rw [split t.basis,lowv,dkeep,dv,hi,Bool.toNat_false,Nat.add_zero,h2P]
  have mle := Nat.mod_le (regValue R.T s.basis) P
  have dle : regValue R.T s.basis/P≤1 := by
    have := Nat.div_lt_of_lt_mul (show regValue R.T s.basis<P*2 by omega); omega
  generalize regValue R.T s.basis%P=M at *
  generalize regValue R.T s.basis/P=D at *
  generalize regValue R.T s.basis=TV at *
  generalize regValue (R.dlo++R.zA) s.basis=AV at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp dle with e|e
  · subst e; simp only [Nat.mul_zero,Nat.add_zero] at md ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · subst e; simp only [Nat.mul_one] at md ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem pow_two_mul_split (h : Nat) (hh : 1≤h) : 2^h=2*2^(h-1) := by
  rw [← pow_succ']; congr 1; omega

theorem raw_lo_le (h a : Nat) (hh : 1≤h) (ha : a<2^h) : DiagSq.rawValue h a+2^h≤2^(2*h) := by
  unfold DiagSq.rawValue signedDiagValue
  rw [if_neg (by omega)]
  have hP : 2^h=2*2^(h-1) := pow_two_mul_split h hh
  have hPP : 2^(2*h)=2^h*2^h := by rw [two_mul,pow_add]
  rw [hPP,hP]; rw [hP] at ha
  generalize 2^(h-1)=Q at *
  have Qpos : 0<Q := by omega
  have vlt : a%Q<Q := Nat.mod_lt _ Qpos
  have adiv := Nat.mod_add_div a Q
  obtain ⟨k,hk⟩ : ∃k,Q=a%Q+1+k := ⟨Q-1-a%Q,by omega⟩
  have e1 : Q-1-a%Q=k := by omega
  rw [e1]
  have t1 : a/Q≤1 := by have := Nat.div_lt_of_lt_mul (show a<Q*2 by omega); omega
  generalize a%Q=v at *
  subst hk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp t1 with e|e
  · have av : a=v := by rw [e] at adiv; omega
    subst av
    nlinarith [Nat.zero_le (a*k),Nat.zero_le (k*k),Nat.zero_le (a*a)]
  · have av : a=v+(v+1+k) := by rw [e] at adiv; omega
    subst av
    nlinarith [Nat.zero_le (v*k),Nat.zero_le (k*k),Nat.zero_le (v*v)]

theorem raw_hi_ge (h S : Nat) (hh : 1≤h) (hS : S<2^(h+1)) :
    2^(2*h)≤DiagSq.rawValue (h+1) S%2^(2*h+1)+2^h := by
  unfold DiagSq.rawValue signedDiagValue
  rw [if_neg (by omega),show h+1-1=h by omega]
  have h1 : 2^(h+1)=2*2^h := by rw [pow_succ]; ring
  have hPP : 2^(2*h)=2^h*2^h := by rw [two_mul,pow_add]
  have hM : 2^(2*h+1)=2*(2^h*2^h) := by rw [pow_succ,hPP]; ring
  rw [h1] at hS ⊢; rw [hPP,hM]
  generalize 2^h=P at *
  have Ppos : 0<P := by omega
  have ult : S%P<P := Nat.mod_lt _ Ppos
  have sdiv := Nat.mod_add_div S P
  obtain ⟨k,hk⟩ : ∃k,P=S%P+1+k := ⟨P-1-S%P,by omega⟩
  have e1 : P-1-S%P=k := by omega
  rw [e1]
  have t1 : S/P≤1 := by have := Nat.div_lt_of_lt_mul (show S<P*2 by omega); omega
  generalize S%P=u at *
  subst hk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp t1 with e|e
  · have sv : S=u := by rw [e] at sdiv; omega
    subst sv
    have lt : S^2+(S+k*(2*(S+1+k)))<2*((S+1+k)*(S+1+k)) := by
      nlinarith [Nat.zero_le (S*k),Nat.zero_le (k*k),Nat.zero_le (S*S)]
    rw [Nat.mod_eq_of_lt lt]
    nlinarith [Nat.zero_le (S*k),Nat.zero_le (k*k),Nat.zero_le (S*S)]
  · have sv : S=u+(u+1+k) := by rw [e] at sdiv; omega
    subst sv
    have ge : 2*((u+1+k)*(u+1+k))≤(u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k))) := by
      nlinarith [Nat.zero_le (u*k),Nat.zero_le (k*k),Nat.zero_le (u*u)]
    have lt : (u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k)))-2*((u+1+k)*(u+1+k))<2*((u+1+k)*(u+1+k)) := by
      have : (u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k)))<2*((u+1+k)*(u+1+k))+2*((u+1+k)*(u+1+k)) := by
        nlinarith [Nat.zero_le (u*k),Nat.zero_le (k*k),Nat.zero_le (u*u)]
      omega
    rw [Nat.mod_eq_sub_mod ge,Nat.mod_eq_of_lt lt]
    have : (u+1+k)*(u+1+k)+2*((u+1+k)*(u+1+k))≤(u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k)))+(u+1+k) := by
      nlinarith [Nat.zero_le (u*k),Nat.zero_le (k*k),Nat.zero_le (u*u)]
    omega

/-- The bound used by `m6w`/`c6w`: the subtracted diagonal seed never exceeds the low
`2h+1` bits of the sum-square seed. -/
theorem raw_low_bound (h a b : Nat) (hh : 1≤h) (ha : a<2^h) (hb : b<2^h) :
    DiagSq.rawValue h a≤DiagSq.rawValue (h+1) (a+b)%2^(2*h+1) ∧ DiagSq.rawValue h a<2^(2*h) := by
  have x := raw_lo_le h a hh ha
  have y := raw_hi_ge h (a+b) hh (by rw [pow_succ]; omega)
  have p : 0<2^h := by positivity
  constructor <;> omega

end ECDSAAdd.Entrant.KRegs
end

section
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

theorem subloW_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S TN : Nat) (hX : A<2^R.dlo.length) (hAe : 2∣A) (hT : TN<2^R.T.length)
    (hb : A≤TN%2^(R.T.length-1)) (hA' : A<2^(R.T.length-1)) :
    Transition R base (vec A B S (TN : Int)) (vec A B S ((TN : Int)-A)) R.m6w := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have tv := ht.exact 3 TN rfl hT
  change regValue R.T t.basis=TN at tv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have av : regValue (R.dlo++R.zA) t.basis=A := by rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero]
  have l := R.lo_lens w
  have c := R.m6w_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0) (by rw [av]; exact hA') (by rw [av,tv]; exact hb)
  have r : Update R.T (-(regValue (R.dlo++R.zA) t.basis : Int)) t (run R.m6w rec t) := by
    have vl := regValue_lt (R.dlo++R.zA) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dlo++R.zA) t.basis) (by omega)
  rw [av] at r
  have act := ht.advance hn 3 (-(A : Int)) r
  simpa only [show (vec A B S (TN : Int)) 3=(TN : Int) from rfl,vec3,sub_eq_add_neg] using act

theorem addloW_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (Z : Nat) (hX : A<2^R.dlo.length) (hAe : 2∣A) (hZ : T+A=Z)
    (hZlt : Z<2^R.T.length) (hb : A≤Z%2^(R.T.length-1)) (hA' : A<2^(R.T.length-1)) :
    Transition R base (vec A B S T) (vec A B S (T+A)) R.c6w := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have AZ : A≤Z := le_trans hb (Nat.mod_le _ _)
  have tv := ht.exact 3 (Z-A) (by simp only [vec]; push_cast [AZ]; omega) (by change Z-A<2^R.T.length; omega)
  change regValue R.T t.basis=Z-A at tv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have av : regValue (R.dlo++R.zA) t.basis=A := by rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero]
  have Ppos : 0<2^(R.T.length-1) := by positivity
  have low : (Z-A)%2^(R.T.length-1)+A<2^(R.T.length-1) := by
    have md := Nat.mod_add_div Z (2^(R.T.length-1))
    have ml := Nat.mod_lt Z Ppos
    generalize 2^(R.T.length-1)=P at *
    generalize Z%P=M at *
    generalize Z/P=D at *
    have e : Z-A=(M-A)+P*D := by omega
    rw [e,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega)]
    omega
  have c := R.c6w_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0) (by rw [av]; exact hA') (by rw [av,tv]; exact low)
  have r : Update R.T (regValue (R.dlo++R.zA) t.basis : Int) t (run R.c6w rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [av] at r
  have act := ht.advance hn 3 ((A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

end ECDSAAdd.Entrant.DiagSq
end

namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-- A register whose value is congruent to an even integer modulo `2^len` (`len ≥ 1`) has
its lowest wire clear. -/
theorem head_false_of_modEq (r : List Wire) (st : BasisState) (T : Int) (hl : 1≤r.length)
    (hv : (regValue r st : Int) ≡ T [ZMOD (2^r.length : Nat)]) (hT : (2:Int)∣T) :
    st (r.headD 0)=false := by
  have h2 : (2:Int)∣((2^r.length : Nat) : Int) := by
    push_cast; exact dvd_pow_self 2 (by omega)
  have hd : (2:Int)∣(regValue r st : Int) := by
    have m := (Int.ModEq.dvd hv.symm)
    have := dvd_trans h2 m
    have e : (regValue r st : Int)=T+((regValue r st : Int)-T) := by ring
    rw [e]; exact dvd_add hT this
  obtain ⟨k,hk⟩ := hd
  have hk' : regValue r st=2*k.toNat := by omega
  have ne : r≠[] := by intro e; rw [e] at hl; simp at hl
  have := LowZero.head_false_of_even r [] st k.toNat hk' ne
  simpa using this

theorem addhiZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) (hTe : (2:Int)∣T) :
    Transition R base (vec A B S T) (vec A B S (T+B)) R.c7g := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have t0 : t.basis (R.T.headD 0)=false :=
    head_false_of_modEq R.T t.basis T (by omega) (ht.value 3) hTe
  have c := R.c7g_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [t0]; exact Bool.and_false _) ((ht.cin hn).trans hi0)
  have r : Update R.T (regValue (R.dhi++R.zB) t.basis : Int) t (run R.c7g rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem rawValue_even (n x : Nat) (hn : 1≤n) : 2∣rawValue n x := by
  unfold rawValue signedDiagValue
  rw [if_neg (by omega)]
  have h1 : 2∣x^2+x := by
    rw [show x^2+x=x*(x+1) by ring]; exact (Nat.even_mul_succ_self x).two_dvd
  have h2 : 2∣(2^(n-1)-1-x%2^(n-1))*2^n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
  rw [show x^2+(x+(2^(n-1)-1-x%2^(n-1))*2^n)=(x^2+x)+(2^(n-1)-1-x%2^(n-1))*2^n by ring]
  exact dvd_add h1 h2

theorem subloZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) (hAe : 2∣A) :
    Transition R base (vec A B S T) (vec A B S (T-A)) R.m6z := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have l := R.lo_lens w
  have c := R.m6z_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (-(regValue (R.dlo++R.zA) t.basis : Int)) t (run R.m6z rec t) := by
    have vl := regValue_lt (R.dlo++R.zA) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dlo++R.zA) t.basis) (by omega)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem subhiZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) (hBe : 2∣B) :
    Transition R base (vec A B S T) (vec A B S (T-B)) R.m7g := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dhi++R.zB).headD 0)=false := by
    obtain ⟨k,hk⟩ := hBe
    exact LowZero.head_false_of_even R.dhi R.zB t.basis k (by rw [xv,hk]) (R.dhi_neg w)
  have l := R.t_lensg w
  have c := R.m7g_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (-(regValue (R.dhi++R.zB) t.basis : Int)) t (run R.m7g rec t) := by
    have vl := regValue_lt (R.dhi++R.zB) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dhi++R.zB) t.basis) (by omega)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem addloZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) (hAe : 2∣A) :
    Transition R base (vec A B S T) (vec A B S (T+A)) R.c6z := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have c := R.c6z_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (regValue (R.dlo++R.zA) t.basis : Int) t (run R.c6z rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act


theorem head_eq_of_modEq (r r' : List Wire) (st : BasisState) (T : Int) (hl : 1≤r.length) (hl' : 1≤r'.length)
    (hv : (regValue r st : Int) ≡ T [ZMOD (2^r.length : Nat)]) (hT : (2:Int)∣T-regValue r' st) :
    st (r.headD 0)=st (r'.headD 0) := by
  have h2 : (2:Int)∣((2^r.length : Nat) : Int) := by
    push_cast; exact dvd_pow_self 2 (by omega)
  have d1 : (2:Int)∣(regValue r st : Int)-T := dvd_trans h2 (Int.ModEq.dvd hv.symm)
  have d : (2:Int)∣(regValue r st : Int)-regValue r' st := by
    have e : (regValue r st : Int)-regValue r' st=((regValue r st : Int)-T)+(T-regValue r' st) := by ring
    rw [e]; exact dvd_add d1 hT
  have ne : r≠[] := by intro e; rw [e] at hl; simp at hl
  have ne' : r'≠[] := by intro e; rw [e] at hl'; simp at hl'
  have a := LowZero.head_bit r [] st ne
  have b := LowZero.head_bit r' [] st ne'
  simp only [List.append_nil] at a b
  rw [a,b]
  have : regValue r st%2=regValue r' st%2 := by omega
  rw [this]

theorem sq_sub_even (a : Nat) : (2:Int)∣((a^2 : Nat) : Int)-(a : Int) := by
  have h : 2∣a^2+a := by
    rw [show a^2+a=a*(a+1) by ring]; exact (Nat.even_mul_succ_self a).two_dvd
  have h' : (2:Int)∣((a^2+a : Nat) : Int) := by exact_mod_cast h
  push_cast at h' ⊢
  have e : (a:Int)^2-a=((a:Int)^2+a)-2*a := by ring
  rw [e]; exact dvd_sub h' (dvd_mul_right 2 _)

theorem dsubloZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hAe : (2:Int)∣A) :
    Transition R base (vec A B S T) (vec (A-(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (dSubZ R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have e := dSubZ_run R.lo R.dlo R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (head_false_of_modEq R.dlo t.basis A (by omega) (ht.value 0) hAe)
  rw [e]
  exact diagsublo_transition R w he hn base hc0 hi0 A B S T t rec ht

theorem dsubhiZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hBe : (2:Int)∣B) :
    Transition R base (vec A B S T) (vec A (B-(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (dSubZ R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have e := dSubZ_run R.hi R.dhi R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (head_false_of_modEq R.dhi t.basis B (by omega) (ht.value 1) hBe)
  rw [e]
  exact diagsubhi_transition R w he hn base hc0 hi0 A B S T t rec ht

theorem daddloZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hAp : (2:Int)∣A-regValue R.lo base.basis) :
    Transition R base (vec A B S T) (vec (A+(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (dAddZ R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have hb := head_eq_of_modEq R.dlo R.lo t.basis A (by omega) (by omega) (ht.value 0) (by rw [xv]; exact hAp)
  have e := dAddZ_run R.lo R.dlo R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (by
      intro y ys' ey hx
      have h1 : t.basis (R.dlo.headD 0)=true := by rw [hb]; exact hx
      rw [ey] at h1; simpa using h1)
  rw [e]
  exact diagaddlo_transition R w he hn base hc0 hi0 A B S T t rec ht

theorem daddhiZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hBp : (2:Int)∣B-regValue R.hi base.basis) :
    Transition R base (vec A B S T) (vec A (B+(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (dAddZ R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have hb := head_eq_of_modEq R.dhi R.hi t.basis B (by omega) (by omega) (ht.value 1) (by rw [xv]; exact hBp)
  have e := dAddZ_run R.hi R.dhi R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (by
      intro y ys' ey hx
      have h1 : t.basis (R.dhi.headD 0)=true := by rw [hb]; exact hx
      rw [ey] at h1; simpa using h1)
  rw [e]
  exact diagaddhi_transition R w he hn base hc0 hi0 A B S T t rec ht

section TopBit
set_option maxHeartbeats 1000000

theorem ccx_as_cx_top (a b t y : Wire) (p : Program) (m : List Bool) (s : State)
    (h : (s.basis a && s.basis b)=s.basis y) : run (.CCX a b t::p) m s=run (.CX y t::p) m s := by
  simp only [run,h]

/-- `incr1` with its second-bit carry Toffoli `CCX y' c c'` replaced by a CNOT. On the 3-bit top field that
`correctionZ` increments (the only width it is used at), the copy is `CX y'' c'`: valid when the field
`y + 2 y' + 4 y''` plus one has a clear top bit, so that `y AND y' = y''` (`incr2_run`). The wider arm is never
instantiated; it uses `CX y' c'` only so that the resource lemmas need no width hypothesis. -/
def incr2 (ys carry : List Wire) (cin : Wire) : Program :=
  match ys, carry with
  | [y,y',y''], c::c'::cs => [.CX y c,.CX cin c]++(.CX y'' c'::
      (mappedAdd [⟨none,false⟩] [y''] cs c'++mappedEraseCarry ⟨none,false⟩ y' c c'++
        mappedSum ⟨none,false⟩ y' c))++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin
  | y::y'::y''::y3::ys', c::c'::cs => [.CX y c,.CX cin c]++(.CX y' c'::
      (mappedAdd [⟨none,false⟩] (y''::y3::ys') cs c'++mappedEraseCarry ⟨none,false⟩ y' c c'++
        mappedSum ⟨none,false⟩ y' c))++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin
  | ys, carry => incr1 ys carry cin

theorem incr2_split (y y' y'' c c' cin : Wire) (ys cs : List Wire) :
    incr1 (y::y'::y''::ys) (c::c'::cs) cin=[.CX y c,.CX cin c]++(.CCX y' c c'::
      (mappedAdd [⟨none,false⟩] (y''::ys) cs c'++mappedEraseCarry ⟨none,false⟩ y' c c'++
        mappedSum ⟨none,false⟩ y' c))++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin := by
  simp [incr1,mappedConstant,mappedAdd,mappedMajority,mappedConstantBit,List.append_assoc]

theorem incr2_run (y y' y'' c c' cin : Wire) (cs : List Wire) (s : State) (m : List Bool)
    (h1 : y'≠c) (h2 : y''≠c) (h3 : cin≠c) (hc : s.basis c=false) (hi : s.basis cin=false)
    (hv : (s.basis y && s.basis y')=s.basis y'') :
    run (incr2 [y,y',y''] (c::c'::cs) cin) m s=run (incr1 [y,y',y''] (c::c'::cs) cin) m s := by
  rw [incr2_split]
  simp only [incr2,List.append_assoc,List.cons_append,List.nil_append]
  let t1 : State := ⟨s.phase,writeBit s.basis c (s.basis c ^^ s.basis y)⟩
  let t2 : State := ⟨t1.phase,writeBit t1.basis c (t1.basis c ^^ t1.basis cin)⟩
  have e : (t2.basis y' && t2.basis c)=t2.basis y'' := by
    simp only [t2,t1,writeBit,Function.update,h1,h2,h3,dif_neg,if_false,dite_false,ne_eq,not_false_eq_true,
      if_true,dite_true,hc,hi]
    simp only [Bool.false_xor,Bool.xor_false]
    rw [← hv, Bool.and_comm]
  exact (ccx_as_cx_top y' c c' y'' _ m t2 e).symm

theorem incr2_mem (ys carry : List Wire) (cin : Wire) :
    ∀i∈incr2 ys carry cin,i∈incr1 ys carry cin∨∃ a b,i=.CX a b ∧ a∈ys ∧ b∈carry := by
  match ys, carry with
  | [y,y',y''], c::c'::cs =>
    rw [incr2_split]
    intro i h
    simp only [incr2,List.mem_append,List.mem_cons] at h ⊢
    rcases h with ((h|h|h)|h)|h
    · tauto
    · right; exact ⟨y'',c',h,by simp,by simp⟩
    · tauto
    · tauto
    · tauto
  | y::y'::y''::y3::ys', c::c'::cs =>
    rw [incr2_split]
    intro i h
    simp only [incr2,List.mem_append,List.mem_cons] at h ⊢
    rcases h with ((h|h|h)|h)|h
    · tauto
    · right; exact ⟨y',c',h,by simp,by simp⟩
    · tauto
    · tauto
    · tauto
  | [], _ => intro i h; exact Or.inl h
  | [_], _ => intro i h; exact Or.inl h
  | [_,_], _ => intro i h; exact Or.inl h
  | [_,_,_], [] => intro i h; exact Or.inl h
  | _::_::_::_::_, [] => intro i h; exact Or.inl h
  | [_,_,_], [_] => intro i h; exact Or.inl h
  | _::_::_::_::_, [_] => intro i h; exact Or.inl h

theorem incr2_counts (ys carry : List Wire) (cin : Wire) (h3 : 3≤ys.length) (hc : 2≤carry.length) :
    toffoliCount (incr2 ys carry cin)+1=toffoliCount (incr1 ys carry cin) ∧
    measurementCount (incr2 ys carry cin)=measurementCount (incr1 ys carry cin) := by
  match ys, carry, h3, hc with
  | [y,y',y''], c::c'::cs, _, _ =>
    rw [incr2_split]
    simp only [incr2,toffoliCount_append,measurementCount_append]
    simp [toffoliCount,measurementCount]
    omega
  | y::y'::y''::y3::ys', c::c'::cs, _, _ =>
    rw [incr2_split]
    simp only [incr2,toffoliCount_append,measurementCount_append]
    simp [toffoliCount,measurementCount]
    omega

theorem incr2_slots (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (incr2 ys carry cin)=Challenge.gateSlots (incr1 ys carry cin) := by
  match ys, carry with
  | [y,y',y''], c::c'::cs =>
    rw [incr2_split]
    simp only [incr2,Challenge.gateSlots_append]
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  | y::y'::y''::y3::ys', c::c'::cs =>
    rw [incr2_split]
    simp only [incr2,Challenge.gateSlots_append]
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  | [], _ => rfl
  | [_], _ => rfl
  | [_,_], _ => rfl
  | [_,_,_], [] => rfl
  | _::_::_::_::_, [] => rfl
  | [_,_,_], [_] => rfl
  | _::_::_::_::_, [_] => rfl

/-- If `L + P*(F+1) ≡ n (mod 8P)` with `L < P`, `n < 4P` and `F` the 3-bit field `b0 + 2 b1 + 4 b2`, then
`b0 AND b1 = b2`. -/
theorem top_field (P L n : Nat) (b0 b1 b2 : Bool) (hL : L<P) (hn : n<4*P)
    (hm : ((8*P : Nat) : Int)∣(n : Int)-(((L+P*((if b0 then 1 else 0)+2*((if b1 then 1 else 0)+
      2*((if b2 then 1 else 0)+2*0))) : Nat) : Int)+((P : Nat) : Int))) :
    (b0 && b1)=b2 := by
  obtain ⟨k,hk⟩ := hm
  have hP : (0 : Int)<P := by exact_mod_cast (show 0<P by omega)
  have hL' : (L : Int)<P := by exact_mod_cast hL
  have hn' : (n : Int)<4*P := by exact_mod_cast hn
  have hn0 : (0 : Int)≤n := by positivity
  have hL0 : (0 : Int)≤L := by positivity
  cases b0 <;> cases b1 <;> cases b2 <;> simp at hk ⊢ <;>
    (rcases le_or_gt 0 k with h|h <;> nlinarith)

def correctionZ2 (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h ++
    incr2 (dst.drop (2*h-1)) (carry.take 2) cin

theorem correctionZ2_run (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0)
    (n : Nat) (hnl : n<2^(2*h+1))
    (hT : (regValue dst s.basis : Int)-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)+
      (2^(2*h-1) : Nat) ≡ n [ZMOD (2^dst.length : Nat)]) :
    run (correctionZ2 h as bs ss dst carry q cin) m s=run (correctionZ h as bs ss dst carry q cin) m s := by
  have r := sharedSub_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s
    (m.take (measurementCount (loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
      (correctionBits h ss q) dst (carry.take (h+1)) h))) hv hq0 hi0 hc0
  have out (w : Wire) (hw : w∈cin::carry) : w∉dst :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have h1 : 1≤h := by rcases hh with rfl|rfl <;> omega
  have hd3 : (dst.drop (2*h-1)).length=3 := by simp only [List.length_drop]; omega
  have hc2 : (carry.take 2).length=2 := by simp only [List.length_take]; omega
  obtain ⟨y,y',y'',ey⟩ := List.length_eq_three.mp hd3
  obtain ⟨c,c',ec⟩ := List.length_eq_two.mp hc2
  have ym : ∀w∈[y,y',y''],w∈dst := fun w hw => List.mem_of_mem_drop (by rw [ey]; exact hw)
  have cm : c∈carry := List.mem_of_mem_take (by rw [ec]; simp)
  have cnd : c∉dst := out c (by simp [cm])
  have cind : cin≠c := fun e => (List.nodup_cons.mp hn).1 (by rw [e]; simp [cm])
  have e8 : 2^dst.length=8*2^(2*h-1) := by
    rw [hdl,show 2*h+2=(2*h-1)+3 by omega,pow_add]; ring
  have e4 : 2^(2*h+1)=4*2^(2*h-1) := by
    rw [show 2*h+1=(2*h-1)+2 by omega,pow_add]; ring
  have key : ∀u : State,Update dst (-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)) s u →
      ∀m',run (incr2 (dst.drop (2*h-1)) (carry.take 2) cin) m' u=run (incr1 (dst.drop (2*h-1)) (carry.take 2) cin) m' u := by
    intro u hu m'
    have comb := (hu.2.2.add_right ((2^(2*h-1) : Nat) : Int)).trans (by convert hT using 1; ring)
    have dv := comb.dvd
    have sp := rv_split dst (2*h-1) (by omega) u.basis
    rw [ey] at sp
    have lt := regValue_lt (dst.take (2*h-1)) u.basis
    rw [List.length_take,Nat.min_eq_left (by omega)] at lt
    rw [sp,e8] at dv
    have tf := top_field (2^(2*h-1)) (regValue (dst.take (2*h-1)) u.basis) n (u.basis y) (u.basis y') (u.basis y'')
      lt (by omega) dv
    rw [ey,ec]
    apply incr2_run _ _ _ _ _ _ []
    · intro e; exact cnd (e ▸ ym y' (by simp))
    · intro e; exact cnd (e ▸ ym y'' (by simp))
    · exact cind
    · exact (hu.2.1 c cnd).trans ((regValue_zero _ _).mp hc0 c cm)
    · exact (hu.2.1 cin (out cin (by simp))).trans hi0
    · exact tf
  simp only [correctionZ2,correctionZ,run_append]
  exact key _ r _

def corrZ2 (R : KRegs) : Program := correctionZ2 R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin

theorem corrZ2_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) (n : Nat)
    (hnl : n<2^(2*R.h+1))
    (hb : T-((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)+
      (2^(2*R.h-1) : Nat)=n) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) n) (corrZ2 R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hzl := w.z
  have hhi : R.hi.length=R.h := by omega
  have hs : R.S.length=R.h+1 := by omega
  have qm : parity R∈R.z := getD_in R.z 0 (by omega)
  have qsub : List.Sublist [parity R] R.z := List.singleton_sublist.mpr qm
  have cn : (R.cin::parity R::R.lo++R.hi++R.S++R.T++R.carry).Nodup := knd hn (fun q => by
    have c := R.counts q; have z := qsub.count_le q
    simp only [KRegs.all,List.count_cons,List.count_append,List.count_nil] at c z ⊢; omega)
  have av := regValue_lt R.lo base.basis
  have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hhi] at bv
  have slt : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [hs,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) slt
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have zv := (ht.keep hn R.z (by intro q h; simp [h])).trans hz0
  have tv := ht.value 3
  change (regValue R.T t.basis : Int) ≡ T [ZMOD (2^R.T.length : Nat)] at tv
  have e : run (corrZ2 R) rec t=run (corrZ R) rec t :=
    correctionZ2_run R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin hh L0 hhi hs (by omega) (by omega) cn t rec
      (by rw [sv,al,bl]) ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv n hnl
      (by rw [al,bl,← hb]; exact (tv.sub_right _).add_right _)
  rw [e]
  have := corrZ_transition R w he hh hn base hz0 hc0 hi0 A B T t rec ht
  rwa [hb] at this

theorem corrZ2_mem (R : KRegs) :
    ∀i∈corrZ2 R,i∈corr R∨∃ a b,i=.CX a b ∧ a∈R.T ∧ b∈R.carry := by
  intro i h
  simp only [corrZ2,correctionZ2,List.mem_append] at h
  rcases h with h|h
  · exact Or.inl (corrZ_mem R i (by simp only [corrZ,correctionZ,List.mem_append]; exact Or.inl h))
  · rcases incr2_mem _ _ _ i h with h|⟨a,b,e,ha,hb⟩
    · exact Or.inl (corrZ_mem R i (by simp only [corrZ,correctionZ,List.mem_append]; exact Or.inr h))
    · exact Or.inr ⟨a,b,e,List.mem_of_mem_drop ha,List.mem_of_mem_take hb⟩

theorem corrZ2_counts (R : KRegs) (w : R.W) :
    toffoliCount (corrZ2 R)+1=toffoliCount (corrZ R) ∧ measurementCount (corrZ2 R)=measurementCount (corrZ R) := by
  have hTl := w.T; have hSl := w.S; have hcl := w.carry; have hh2 := w.hh; have h5 := w.h5
  have a := incr2_counts (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
    (by simp only [List.length_drop]; have h4 := w.h4; omega)
    (by simp only [List.length_take]; omega)
  simp only [corrZ2,corrZ,correctionZ2,correctionZ,toffoliCount_append,measurementCount_append]
  omega

theorem corrZ2_slots (R : KRegs) : Challenge.gateSlots (corrZ2 R)=Challenge.gateSlots (corrZ R) := by
  have a := incr2_slots (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  simp only [corrZ2,corrZ,correctionZ2,correctionZ,Challenge.gateSlots_append]
  omega

theorem wires_sub_of {p q : Program} (h : ∀i∈p,i.wires⊆wires q) : wires p⊆wires q := by
  induction p with
  | nil => simp [wires]
  | cons i p ih =>
    simp only [wires]
    exact Finset.union_subset (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem instr_wires_sub {i : Instr} {q : Program} (h : i∈q) : i.wires⊆wires q := by
  induction q with
  | nil => simp at h
  | cons j q ih =>
    simp only [wires]
    rcases List.mem_cons.mp h with e|h
    · subst e; exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

theorem incr2_wires_le (ys carry : List Wire) (cin : Wire) :
    wires (incr2 ys carry cin)⊆wires (incr1 ys carry cin) := by
  apply wires_sub_of
  intro i hi
  match ys, carry with
  | [y,y',y''], c::c'::cs =>
    have hm : Instr.CX c' y''∈incr1 [y,y',y''] (c::c'::cs) cin := by
      rw [incr2_split]; simp [mappedAdd,mappedSum]
    rw [incr2_split] at hm ⊢
    simp only [incr2,List.mem_append,List.mem_cons] at hi
    rcases hi with ((h|h|h)|h)|h
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · subst h
      show ({y'',c'} : Finset Wire)⊆_
      rw [Finset.pair_comm]
      exact instr_wires_sub hm
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
  | y::y'::y''::y3::ys', c::c'::cs =>
    have hm : Instr.CCX y' c c'∈incr1 (y::y'::y''::y3::ys') (c::c'::cs) cin := by
      rw [incr2_split]; simp
    rw [incr2_split] at hm ⊢
    simp only [incr2,List.mem_append,List.mem_cons] at hi
    rcases hi with ((h|h|h)|h)|h
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · subst h
      refine Finset.Subset.trans ?_ (instr_wires_sub hm)
      intro q hq
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq ⊢
      tauto
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
  | [], _ => exact instr_wires_sub hi
  | [_], _ => exact instr_wires_sub hi
  | [_,_], _ => exact instr_wires_sub hi
  | [_,_,_], [] => exact instr_wires_sub hi
  | _::_::_::_::_, [] => exact instr_wires_sub hi
  | [_,_,_], [_] => exact instr_wires_sub hi
  | _::_::_::_::_, [_] => exact instr_wires_sub hi

theorem corrZ2_wires (R : KRegs) : wires (corrZ2 R)⊆wires (corrZ R) := by
  simp only [corrZ2,corrZ,correctionZ2,correctionZ,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (incr2_wires_le _ _ _)

theorem corrZ2_physical (R : KRegs) (hn : R.all.Nodup) (h : GatePhysical (corr R)) : GatePhysical (corrZ2 R) := by
  intro i hi
  rcases corrZ2_mem R i hi with hi|⟨a,b,rfl,ha,hb⟩
  · exact h i hi
  · show a≠b
    intro e; subst e
    exact kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) a ha hb

end TopBit

def headBlockZ (R : KRegs) : Program := seedsT R ++ (R.m6w++R.m7g++corrZ2 R++
  dSubZ R.lo R.dlo R.carry R.cin++dSubZ R.hi R.dhi R.carry R.cin)

/-- `make` with the dead lowest carries of `m6`, `m7`, `m8` dropped. -/
def makeZ (R : KRegs) : Program := headBlockZ R++R.m8g

theorem makeZ_counts_rel (R : KRegs) (w : R.W) :
    toffoliCount (makeZ R)+11+parR R=toffoliCount (make R) ∧ measurementCount (makeZ R)+4+parR R=measurementCount (make R) := by
  have a := R.m6w_counts w; have b := R.m7g_counts w; have c := R.m8g_counts w
  have cz := corrZ_counts R w
  have cz2 := corrZ2_counts R w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hdl := w.dst; have hpl := w.pad; have hh := w.hh; have h5 := w.h5
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have ds1 := dSubZ_counts R.lo R.dlo R.carry R.cin (by omega) (by omega) (by omega)
  have ds2 := dSubZ_counts R.hi R.dhi R.carry R.cin (by omega) (by omega) (by omega)
  have t1 := rawT_counts R.lo R.dlo R.pad R.carry (by simp only [KRegs.lo,List.length_take]; omega)
    (by simp only [KRegs.lo,KRegs.dlo,List.length_take]; omega) hpl
    (by simp only [KRegs.lo,List.length_take]; omega)
  have t2 := rawT_counts R.hi R.dhi R.pad R.carry (by simp only [KRegs.hi,List.length_drop]; omega)
    (by simp only [KRegs.hi,KRegs.dhi,List.length_drop]; omega) hpl
    (by simp only [KRegs.hi,List.length_drop]; omega)
  have t5 := rawT_counts R.S R.T R.pad R.carry (by omega) (by omega) hpl (by omega)
  simp only [makeZ,make,headBlockZ,headBlock,seedsT,seeds,toffoliCount_append,measurementCount_append,parR]
  constructor <;> omega

theorem makeZ_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (makeZ R)+11+parR R=cost R ∧ measurementCount (makeZ R)+4+parR R=cost R := by
  have a := makeZ_counts_rel R w
  have b := make_counts R w he
  constructor <;> omega

theorem rawMakeT_wires_sub (xs dst pad carry : List Wire) :
    wires (rawMakeT xs dst pad carry)⊆wires (rawMake xs dst pad carry) := by
  unfold rawMakeT rawMake
  exact (ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry).1.1.trans (ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry).1

theorem seedsT_wires (R : KRegs) : wires (seedsT R)⊆wires (seeds R) := by
  simp only [seedsT,seeds,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union
    (rawMakeT_wires_sub _ _ _ _) (rawMakeT_wires_sub _ _ _ _)) (subset_refl _)) (rawMakeT_wires_sub _ _ _ _)

theorem makeZ_support (R : KRegs) (w : R.W) : wires (makeZ R)⊆R.all.toFinset := by
  have old := (steps_support R w).1
  have a := R.m6w_wires; have b := R.m7g_wires; have c := R.m8g_wires
  have d := seedsT_wires R
  simp only [make,headBlock,wires_append,Finset.union_subset_iff] at old
  simp only [makeZ,headBlockZ,wires_append,Finset.union_subset_iff]
  obtain ⟨⟨o1,⟨⟨⟨⟨o2,o3⟩,o4⟩,o5⟩,o6⟩⟩,o7⟩ := old
  exact ⟨⟨d.trans o1,⟨⟨⟨⟨a.trans o2,b.trans o3⟩,((corrZ2_wires R).trans (wires_of_mem (corrZ_mem R))).trans o4⟩,(wires_of_mem (dSubZ_mem _ _ _ _)).trans o5⟩,(wires_of_mem (dSubZ_mem _ _ _ _)).trans o6⟩⟩,c.trans o7⟩

theorem makeZ_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeZ R) := by
  have old := (steps_physical R w hn).1
  have oldc := (steps_physical R w hn).2
  simp only [make,headBlock,seeds,rawMake,gatePhysical_append] at old
  simp only [clear,rawClear,gatePhysical_append] at oldc
  simp only [makeZ,headBlockZ,seedsT,gatePhysical_append]
  obtain ⟨⟨⟨⟨⟨⟨l1,l2⟩,⟨h1,h2⟩⟩,sm⟩,⟨s1,s2⟩⟩,⟨⟨⟨⟨o2,o3⟩,o4⟩,o5⟩,o6⟩⟩,o7⟩ := old
  have pl := ECDSAAdd.Entrant.TrimRow.physical R.lo R.dlo R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨l1,l2⟩) (by rw [gatePhysical_append]; exact ⟨l2,by tauto⟩)
  have ph := ECDSAAdd.Entrant.TrimRow.physical R.hi R.dhi R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨h1,h2⟩) (by rw [gatePhysical_append]; exact ⟨h2,by tauto⟩)
  have ps := ECDSAAdd.Entrant.TrimRow.physical R.S R.T R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨s1,s2⟩) (by rw [gatePhysical_append]; exact ⟨s2,by tauto⟩)
  exact ⟨⟨⟨⟨⟨(ECDSAAdd.Entrant.TrimMid.P_side _ _ _ _).1.2.2 pl.1,(ECDSAAdd.Entrant.TrimMid.P_side _ _ _ _).1.2.2 ph.1⟩,sm⟩,
    (ECDSAAdd.Entrant.TrimMid.P_side _ _ _ _).1.2.2 ps.1⟩,⟨⟨⟨⟨R.m6w_physical hn,R.m7g_physical hn⟩,(corrZ2_physical R hn o4)⟩,(fun i hi => o5 i (dSubZ_mem _ _ _ _ i hi))⟩,(fun i hi => o6 i (dSubZ_mem _ _ _ _ i hi))⟩⟩,R.m8g_physical hn⟩

theorem makeZ_slots (R : KRegs) : Challenge.gateSlots (makeZ R)≤Challenge.gateSlots (make R) := by
  have a := R.m6w_slots; have b := R.m7g_slots; have c := R.m8g_slots; have cz := corrZ_slots R
  have cz2 := corrZ2_slots R
  have ds1 := dSubZ_slots R.lo R.dlo R.carry R.cin; have ds2 := dSubZ_slots R.hi R.dhi R.carry R.cin
  have t1 := (rawT_slots R.lo R.dlo R.pad R.carry).1
  have t2 := (rawT_slots R.hi R.dhi R.pad R.carry).1
  have t5 := (rawT_slots R.S R.T R.pad R.carry).1
  simp only [makeZ,make,headBlockZ,headBlock,seedsT,seeds,rawMakeT,rawMake,Challenge.gateSlots_append] at t1 t2 t5 ⊢
  omega

theorem prefixZ_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (headBlockZ R) m s)
      (vec ((regValue R.lo s.basis)^2) ((regValue R.hi s.basis)^2)
        (regValue R.lo s.basis+regValue R.hi s.basis) (2*regValue R.lo s.basis*regValue R.hi s.basis)) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4
  have hhi : R.hi.length=R.h := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let A := rawValue R.h a
  let B := rawValue R.h b
  let S := a+b
  let Z := rawValue (R.h+1) S
  have hA : A<2^R.dlo.length := by
    have v := rawValue_bound R.lo s.basis (by omega)
    simpa only [L0,L2] using v
  have hB : B<2^R.dhi.length := by
    have v := rawValue_bound R.hi s.basis (by omega)
    simpa only [hhi,L3,show 2*(R.bank.length-R.h)=2*R.h by omega] using v
  have alo : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bhi : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have bnd := KRegs.raw_low_bound R.h a b (by omega) alo bhi
  have hT1 : R.T.length=2*R.h+2 := by have := w.T; have := w.S; omega
  have zlt : Z<2^(2*R.h+2) := by
    have x := KRegs.raw_lo_le (R.h+1) S (by omega) (by rw [pow_succ]; dsimp only [S]; omega)
    rw [show 2*(R.h+1)=2*R.h+2 by ring] at x
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (by positivity)) x
  have p2 : 2^(2*R.h)≤2^(2*R.h+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb1 : A≤Z%2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact bnd.1
  have hA1 : A<2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact lt_of_lt_of_le bnd.2 p2
  have hZ1 : Z<2^R.T.length := by rw [hT1]; exact zlt
  have st1 := subloW_transition R w hn s hz0 hc0 hi0 A B S Z hA (rawValue_even _ _ (by omega)) hZ1 hb1 hA1
  have st2 := subhiZ_transition R w hn s hz0 hc0 hi0 A B S ((Z : Int)-A) hB (rawValue_even _ _ (by omega))
  have norm := cross_normalize R.h a b hh alo bhi
  change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
    (2*a*b : Nat) at norm
  have ab2 : 2*a*b<2^(2*R.h+1) := by
    have := Nat.mul_lt_mul'' alo bhi
    rw [show 2*R.h+1=R.h+R.h+1 by omega,pow_succ,pow_add]; nlinarith
  have st3 := corrZ2_transition R w he hh hn s hz0 hc0 hi0 A B ((Z : Int)-A-B) (2*a*b) ab2 norm
  have st4 := dsubloZ_transition R w he hn s hc0 hi0 A B S (2*a*b : Nat) (by exact_mod_cast rawValue_even _ _ (by omega))
  have st4' : Transition R s (vec A B S (2*a*b : Nat)) (vec (a^2 : Nat) B S (2*a*b : Nat))
      (dSubZ R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add,add_sub_cancel_right] using st4
  have st5 := dsubhiZ_transition R w he hn s hc0 hi0 (a^2 : Nat) B S (2*a*b : Nat) (by exact_mod_cast rawValue_even _ _ (by omega))
  have st5' : Transition R s (vec (a^2 : Nat) B S (2*a*b : Nat))
      (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (dSubZ R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add,add_sub_cancel_right] using st5
  have tail := (((st1.seq st2).seq st3).seq st4').seq st5'
  have initial := seedsT_shape R w he hn s (m.take (measurementCount (seedsT R))) hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have result := tail _ (m.drop (measurementCount (seedsT R))) initial
  simpa only [headBlockZ,run_append,A,B,S,Z,a,b,Int.natCast_mul,Int.natCast_add,Int.natCast_pow] using result


theorem makeZ_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (makeZ R) m s).phase=s.phase ∧
    regValue R.dst (run (makeZ R) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.S (run (makeZ R) m s).basis=regValue R.lo s.basis+regValue R.hi s.basis ∧
    regValue R.T (run (makeZ R) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (makeZ R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let f := m.take (measurementCount (headBlockZ R))
  let g := m.drop (measurementCount (headBlockZ R))
  let u := run (headBlockZ R) f s
  have h := prefixZ_shape R w he hh hn s f hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have al : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bl : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  have sq := square_bound (a+b) R.S.length slt
  have tvlt : 2*a*b<2^R.T.length := by rw [hTl]; omega
  have av : regValue R.dlo u.basis=a^2 := h.exact 0 (a^2) (by simp [vec,a,b])
    (by change a^2<2^R.dlo.length; rw [L2]; exact square_bound _ _ al)
  have bv : regValue R.dhi u.basis=b^2 := h.exact 1 (b^2) (by simp [vec,a,b])
    (by change b^2<2^R.dhi.length; rw [L3,show R.bank.length-R.h=R.h by omega]; exact square_bound _ _ bl)
  have sv : regValue R.S u.basis=a+b := h.exact 2 (a+b) (by simp [vec,a,b]) slt
  have tv : regValue R.T u.basis=2*a*b := h.exact 3 (2*a*b) (by simp [vec,a,b]) tvlt
  have dv : regValue R.dst u.basis=a^2+2^(2*R.h)*b^2 := by rw [R.dst_value w,av,bv]
  have cv := (h.keep hn R.carry (by intro q hq; simp [hq])).trans hc0
  have zv := (h.keep hn R.zM (fun q hq => Or.inr (Or.inl (List.mem_of_mem_take hq)))).trans
    (KRegs.xz (r:=R.zM) hz0 (fun q hq => List.mem_of_mem_take hq))
  have r := R.m8g_correct w hn u g (a*b) (fun q hq => (regValue_zero _ _).mp cv q (List.mem_of_mem_take hq))
    (by rw [tv]; ring) ((h.cin hn).trans hi0)
  have rv : regValue R.dmid (run R.m8g g u).basis=
      (2*a*b+(a^2+2^(2*R.h)*b^2)/2^R.h)%2^(2*R.bank.length-R.h) := by
    rw [r.2.2,regValue_append,tv,zv,h.cin hn,hi0,
      show regValue R.dmid u.basis=regValue R.dst u.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by have := w.dst; omega) u.basis,dv,L4]
    simp
  have frame : ∀q,q∉R.dmid → (run R.m8g g u).basis q=u.basis q := r.2.1
  have keepLow : regValue (R.dst.take R.h) (run R.m8g g u).basis=regValue (R.dst.take R.h) u.basis :=
    kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have dfin : regValue R.dst (run R.m8g g u).basis=(regValue R.bank s.basis)^2 := by
    rw [R.bank_value w s.basis,R.dst_value_mid w,rv,keepLow,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by have := w.dst; omega),dv]
    exact KRegs.kfinal a b R.h R.bank.length al (by simpa only [show R.bank.length-R.h=R.h by omega] using bl) (by omega)
  have result : (run R.m8g g u).phase=s.phase ∧ regValue R.dst (run R.m8g g u).basis=(regValue R.bank s.basis)^2 ∧
      regValue R.S (run R.m8g g u).basis=a+b ∧ regValue R.T (run R.m8g g u).basis=2*a*b ∧
      ∀q,q∉R.dst → q∉R.S → q∉R.T → (run R.m8g g u).basis q=s.basis q := by
    refine ⟨r.1.trans h.phase,dfin,?_,?_,?_⟩
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans sv
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans tv
    · intro q hd hs ht
      exact (frame q (fun bad => hd (List.mem_of_mem_drop bad))).trans (h.rest q hd hs ht)
  simpa only [makeZ,run_append,u,f,g,a,b] using result

theorem clearZ_start_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run R.c8g m s) (vec ((regValue R.lo s.basis)^2 : Nat) ((regValue R.hi s.basis)^2 : Nat)
      (regValue R.lo s.basis+regValue R.hi s.basis : Nat) (2*regValue R.lo s.basis*regValue R.hi s.basis : Nat)) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry; have hdl := w.dst
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have al : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bl : b<2^(R.bank.length-R.h) := by simpa only [L1] using regValue_lt R.hi s.basis
  have av : a^2<2^(2*R.h) := square_bound _ _ al
  have hd : regValue R.dst s.basis=(a+2^R.h*b)^2 := by
    simpa only [R.bank_value w s.basis] using hd0
  have XLt : (a+2^R.h*b)^2<2^(2*R.bank.length) := by
    rw [←R.bank_value w s.basis]
    exact square_bound _ _ (regValue_lt R.bank s.basis)
  have hX : (a+2^R.h*b)^2=(a^2+2^(2*R.h)*b^2)+2^R.h*(2*a*b) := by ring
  have hdiv : (a+2^R.h*b)^2/2^R.h=(a^2+2^(2*R.h)*b^2)/2^R.h+2*a*b := by
    rw [hX,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  have hmod : (a+2^R.h*b)^2%2^R.h=(a^2+2^(2*R.h)*b^2)%2^R.h := by
    rw [hX,Nat.add_mul_mod_self_left]
  have hq : (a+2^R.h*b)^2/2^R.h<2^(2*R.bank.length-R.h) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),←pow_add,
      show 2*R.bank.length-R.h+R.h=2*R.bank.length by omega]
    exact XLt
  have r := R.c8g_correct w hn s m (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq))
    (by rw [LowZero.head_false_of_even R.T R.zM s.basis (a*b) (by rw [hT0]; ring) (R.T_neg w)]; rfl) hi0
  have frame : ∀q,q∉R.dmid → (run R.c8g m s).basis q=s.basis q := r.2.1
  have low : regValue (R.dst.take R.h) (run R.c8g m s).basis=regValue (R.dst.take R.h) s.basis := kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have zm : regValue R.zM s.basis=0 := KRegs.xz hz0 (fun q h => List.mem_of_mem_take h)
  have dv : regValue R.dst (run R.c8g m s).basis=a^2+2^(2*R.h)*b^2 := by
    rw [R.dst_value_mid w,
      r.2.2,low,regValue_append,hT0,zm,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by omega),
      show regValue R.dmid s.basis=regValue R.dst s.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by omega) s.basis,hd,L4]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  have dlo : regValue R.dlo (run R.c8g m s).basis=a^2 := by
    rw [show regValue R.dlo (run R.c8g m s).basis=regValue R.dst (run R.c8g m s).basis%2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt av]
  have dhi : regValue R.dhi (run R.c8g m s).basis=b^2 := by
    rw [show regValue R.dhi (run R.c8g m s).basis=regValue R.dst (run R.c8g m s).basis/2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt av,Nat.zero_add]
  have sv := (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans hS0
  have tv := (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans hT0
  refine ⟨r.1,?_,fun q hd _ _ => frame q (fun bad => hd (List.mem_of_mem_drop bad))⟩
  intro i; fin_cases i
  · change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
    rw [dlo]; exact Int.ModEq.rfl
  · change (regValue R.dhi _ : Int) ≡ _ [ZMOD _]
    rw [dhi]; exact Int.ModEq.rfl
  · change (regValue R.S _ : Int) ≡ _ [ZMOD _]
    rw [sv]; exact Int.ModEq.rfl
  · change (regValue R.T _ : Int) ≡ _ [ZMOD _]
    rw [tv]; exact Int.ModEq.rfl


end ECDSAAdd.Entrant.DiagSq


section
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-! Bit 1 of the clear-side diagonal add. In `dAddZ xs dst` with `dst ≡ X² (mod 8)` the bit-0
carry is `x₀` (already a copy in `addHead0`) and the bit-1 majority fires on
`(y₁ ⊕ x₁) ∧ (x₀ ⊕ x₁) = x₁ ∧ ¬x₀ = y₂`: its Toffoli is the CNOT `y₂ → c₁`. -/

def head1Pre (a y cin c a1 y1 : Wire) : Program :=
  [.CX a y,.CX a cin,.CX a c,.CX a cin,.CX a y,.CX a1 y1,.CX a1 c]

def head1Post (a y cin c a1 y1 c1 : Wire) (b'' : MappedBit) (bits : List MappedBit)
    (y2 : Wire) (ys cs : List Wire) : Program :=
  [.CX a1 c1,.CX a1 c,.CX a1 y1]++(mappedAdd (b''::bits) (y2::ys) cs c1++
    mappedEraseCarry ⟨some a1,false⟩ y1 c c1++mappedSum ⟨some a1,false⟩ y1 c)++
    mappedEraseCarry ⟨some a,false⟩ y cin c++mappedSum ⟨some a,false⟩ y cin

def addHead1 (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
  match bits, ys, carry with
  | ⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits', y::y1::y2::y3::ys', c::c1::c2::cs =>
      head1Pre a y cin c a1 y1++(.CX y2 c1::head1Post a y cin c a1 y1 c1 b'' (b3::bits') y2 (y3::ys') (c2::cs))
  | bits, ys, carry => addHead0 bits ys carry cin

theorem addHead0_split1 (a y cin c a1 y1 c1 : Wire) (b'' : MappedBit) (bits : List MappedBit)
    (y2 : Wire) (ys cs : List Wire) :
    addHead0 (⟨some a,false⟩::⟨some a1,false⟩::b''::bits) (y::y1::y2::ys) (c::c1::cs) cin=
      head1Pre a y cin c a1 y1++(.CCX y1 c c1::head1Post a y cin c a1 y1 c1 b'' bits y2 ys cs) := by
  simp [addHead0,maj0,mappedAdd,mappedMajority,majority,head1Pre,head1Post,List.append_assoc]

theorem ccx_as_cx (a b t y : Wire) (p : Program) (m : List Bool) (s : State)
    (h : (s.basis a && s.basis b)=s.basis y) : run (.CCX a b t::p) m s=run (.CX y t::p) m s := by
  simp only [run,h]

theorem addHead1_run (a a1 y y1 y2 y3 c c1 c2 cin : Wire) (b'' b3 : MappedBit) (bits : List MappedBit)
    (ys cs : List Wire) (m : List Bool) (s : State)
    (hd : [a,a1,y,y1,y2,c,cin].Nodup)
    (hcopy : ((s.basis y1 ^^ s.basis a1) && (s.basis c ^^ s.basis a ^^ s.basis a1))=s.basis y2) :
    run (addHead1 (⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits) (y::y1::y2::y3::ys) (c::c1::c2::cs) cin) m s=
      run (addHead0 (⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits) (y::y1::y2::y3::ys) (c::c1::c2::cs) cin) m s := by
  rw [addHead0_split1]
  simp only [addHead1]
  have m0 : measurementCount (head1Pre a y cin c a1 y1)=0 := rfl
  rw [run_append,run_append,m0,List.take_zero,List.drop_zero]
  symm
  apply ccx_as_cx
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,or_false,
    not_false_eq_true,and_true] at hd
  obtain ⟨⟨h1,h2,h3,h4,h5,h6⟩,⟨h7,h8,h9,h10,h11⟩,⟨h12,h13,h14,h15⟩,⟨h16,h17,h18⟩,⟨h19,h20⟩,h21⟩ := hd
  simp only [head1Pre,run,writeBit,Function.update]
  simp [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,
    Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm h5,Ne.symm h6,Ne.symm h7,Ne.symm h8,Ne.symm h9,
    Ne.symm h10,Ne.symm h11,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h15,Ne.symm h16,Ne.symm h17,
    Ne.symm h18,Ne.symm h19,Ne.symm h20,Ne.symm h21] at hcopy ⊢
  try (rw [← hcopy])

theorem diag_cons2 (x x' : Wire) (xs : List Wire) :
    ∃ b'' bits,mappedDiagonal (x::x'::xs)=⟨some x,false⟩::⟨some x',false⟩::b''::bits := by
  cases xs with
  | nil => exact ⟨_,_,rfl⟩
  | cons x'' xs => exact ⟨_,_,rfl⟩

theorem diag_cons3 (x x' : Wire) (xs : List Wire) :
    ∃ b'' b3 bits,mappedDiagonal (x::x'::xs)=⟨some x,false⟩::⟨some x',false⟩::b''::b3::bits := by
  cases xs with
  | nil => exact ⟨_,_,_,rfl⟩
  | cons x'' xs =>
    cases xs with
    | nil => exact ⟨_,_,_,rfl⟩
    | cons x3 xs => exact ⟨_,_,_,rfl⟩

def dAddZ2 (xs dst carry : List Wire) (cin : Wire) : Program :=
  addHead1 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin

/-- The low three bits of `X²`: bit 1 is clear and bit 2 is `x₁ ∧ ¬x₀`. -/
theorem bits_of_sq8 (y0 y1 y2 x0 x1 : Wire) (ys xt : List Wire) (st : BasisState) (A : Int)
    (hv : (regValue (y0::y1::y2::ys) st : Int) ≡ A [ZMOD (2^(y0::y1::y2::ys).length : Nat)])
    (h8 : (8:Int)∣A-((regValue (x0::x1::xt) st : Nat) : Int)^2) :
    ((st y1 ^^ st x1) && (st x0 ^^ st x1))=st y2 := by
  have ey : regValue (y0::y1::y2::ys) st=(if st y0 then 1 else 0)+2*((if st y1 then 1 else 0)+
      2*((if st y2 then 1 else 0)+2*regValue ys st)) := rfl
  have ex : regValue (x0::x1::xt) st=(if st x0 then 1 else 0)+2*((if st x1 then 1 else 0)+
      2*regValue xt st) := rfl
  have d8 : (8:Int)∣((2^(y0::y1::y2::ys).length : Nat) : Int) := by
    have : 2^(y0::y1::y2::ys).length=8*2^ys.length := by
      simp only [List.length_cons,pow_succ]; ring
    rw [this]; push_cast; exact Dvd.intro _ rfl
  have d1 : (8:Int)∣(regValue (y0::y1::y2::ys) st : Int)-A := dvd_trans d8 (Int.ModEq.dvd hv.symm)
  have d2 : (8:Int)∣(regValue (y0::y1::y2::ys) st : Int)-((regValue (x0::x1::xt) st : Nat) : Int)^2 := by
    have e : (regValue (y0::y1::y2::ys) st : Int)-((regValue (x0::x1::xt) st : Nat) : Int)^2=
        ((regValue (y0::y1::y2::ys) st : Int)-A)+(A-((regValue (x0::x1::xt) st : Nat) : Int)^2) := by ring
    rw [e]; exact dvd_add d1 h8
  have hX : ((regValue (x0::x1::xt) st : Nat) : Int)=((if st x0 then 1 else 0)+2*(if st x1 then 1 else 0) : Int)+
      4*(regValue xt st : Int) := by rw [ex]; push_cast; ring
  have hY : ((regValue (y0::y1::y2::ys) st : Nat) : Int)=((if st y0 then 1 else 0)+2*(if st y1 then 1 else 0)+
      4*(if st y2 then 1 else 0) : Int)+8*(regValue ys st : Int) := by rw [ey]; push_cast; ring
  have d4 : (8:Int)∣((if st y0 then 1 else 0)+2*(if st y1 then 1 else 0)+4*(if st y2 then 1 else 0) : Int)-
      ((if st x0 then 1 else 0)+2*(if st x1 then 1 else 0) : Int)^2 := by
    have e : ((if st y0 then 1 else 0)+2*(if st y1 then 1 else 0)+4*(if st y2 then 1 else 0) : Int)-
        ((if st x0 then 1 else 0)+2*(if st x1 then 1 else 0) : Int)^2=
        ((regValue (y0::y1::y2::ys) st : Int)-((regValue (x0::x1::xt) st : Nat) : Int)^2)+
        8*(((if st x0 then 1 else 0)+2*(if st x1 then 1 else 0) : Int)*(regValue xt st : Int)+
          2*(regValue xt st : Int)^2-(regValue ys st : Int)) := by
      rw [hX,hY]; ring
    rw [e]; exact dvd_add d2 (dvd_mul_right 8 _)
  revert d4
  generalize st y0=b0; generalize st y1=b1; generalize st y2=b2; generalize st x0=b3; generalize st x1=b4
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

theorem dAddZ2_run (xs dst carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : 4≤carry.length)
    (hcopy : ∀x0 x1 xt y0 y1 y2 ys c cs,xs=x0::x1::xt → dst=y0::y1::y2::ys →
      carry.take (dst.length-1)=c::cs →
      ((s.basis y1 ^^ s.basis x1) && (s.basis c ^^ s.basis x0 ^^ s.basis x1))=s.basis y2) :
    run (dAddZ2 xs dst carry cin) m s=run (dAddZ xs dst carry cin) m s := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt,xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,y3,ys,rfl⟩ : ∃ y0 y1 y2 y3 ys,dst=y0::y1::y2::y3::ys := by
    match dst, hd with
    | y0::y1::y2::y3::ys, _ => exact ⟨y0,y1,y2,y3,ys,rfl⟩
  obtain ⟨c,c1,c2,cs,hct⟩ : ∃ c c1 c2 cs,carry.take ((y0::y1::y2::y3::ys).length-1)=c::c1::c2::cs := by
    have hl : 3≤(carry.take ((y0::y1::y2::y3::ys).length-1)).length := by
      rw [List.length_take]; simp only [List.length_cons]; omega
    match carry.take ((y0::y1::y2::y3::ys).length-1), hl with
    | c::c1::c2::cs, _ => exact ⟨c,c1,c2,cs,rfl⟩
  obtain ⟨b'',b3,bits,e⟩ := diag_cons3 x0 x1 xt
  have hcm : ∀q∈c::c1::c2::cs,q∈carry := fun q h => List.mem_of_mem_take (hct ▸ h)
  have cnt := fun w => List.nodup_iff_count.mp hn w
  have nd : [x0,x1,y0,y1,y2,c,cin].Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := cnt w
    have tc : [c].count w≤carry.count w := by
      by_cases hw : w=c
      · subst hw; simpa using List.count_pos_iff.mpr (hcm w (by simp))
      · rw [List.count_eq_zero.mpr (by simpa using hw)]; exact Nat.zero_le _
    simp only [List.count_cons,List.count_append,List.count_nil] at h tc ⊢
    omega
  simp only [dAddZ2,dAddZ,e,hct]
  exact addHead1_run x0 x1 y0 y1 y2 y3 c c1 c2 cin b'' b3 bits ys cs m s nd
    (hcopy x0 x1 xt y0 y1 y2 (y3::ys) c (c1::c2::cs) rfl rfl hct)

theorem daddloZ2_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hAp : (2:Int)∣A-regValue R.lo base.basis)
    (h8 : (8:Int)∣A-((regValue R.lo base.basis : Nat) : Int)^2) :
    Transition R base (vec A B S T) (vec (A+(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (dAddZ2 R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have cv := ht.keep hn R.carry (fun q h => Or.inr (Or.inr (Or.inr (Or.inl h))))
  have cz : ∀q∈R.carry,t.basis q=false := (regValue_zero _ _).mp (cv.trans hc0)
  have e := dAddZ2_run R.lo R.dlo R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) (by
      intro x0 x1 xt y0 y1 y2 ys c cs hx hy hcc
      have hcm : c∈R.carry := List.mem_of_mem_take (by rw [hcc]; exact List.mem_cons_self)
      rw [cz c hcm,Bool.false_xor]
      have hv := ht.value 0
      change (regValue R.dlo t.basis : Int) ≡ A [ZMOD (2^R.dlo.length : Nat)] at hv
      rw [hy] at hv
      apply bits_of_sq8 y0 y1 y2 x0 x1 ys xt t.basis A hv
      rw [← hx,xv]; exact h8)
  rw [e]
  exact daddloZ_transition R w he hn base hc0 hi0 A B S T hAp t rec ht

theorem daddhiZ2_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hAp : (2:Int)∣B-regValue R.hi base.basis)
    (h8 : (8:Int)∣B-((regValue R.hi base.basis : Nat) : Int)^2) :
    Transition R base (vec A B S T) (vec A (B+(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (dAddZ2 R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := ht.keep hn R.carry (fun q h => Or.inr (Or.inr (Or.inr (Or.inl h))))
  have cz : ∀q∈R.carry,t.basis q=false := (regValue_zero _ _).mp (cv.trans hc0)
  have e := dAddZ2_run R.hi R.dhi R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) (by
      intro x0 x1 xt y0 y1 y2 ys c cs hx hy hcc
      have hcm : c∈R.carry := List.mem_of_mem_take (by rw [hcc]; exact List.mem_cons_self)
      rw [cz c hcm,Bool.false_xor]
      have hv := ht.value 1
      change (regValue R.dhi t.basis : Int) ≡ B [ZMOD (2^R.dhi.length : Nat)] at hv
      rw [hy] at hv
      apply bits_of_sq8 y0 y1 y2 x0 x1 ys xt t.basis B hv
      rw [← hx,xv]; exact h8)
  rw [e]
  exact daddhiZ_transition R w he hn base hc0 hi0 A B S T hAp t rec ht

theorem dAddZ2_shape (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : 4≤carry.length) :
    ∃ a a1 y y1 y2 c c1 b'' bits ys cs,y2∈dst ∧ c1∈carry ∧
      dAddZ2 xs dst carry cin=head1Pre a y cin c a1 y1++(.CX y2 c1::head1Post a y cin c a1 y1 c1 b'' bits y2 ys cs) ∧
      dAddZ xs dst carry cin=head1Pre a y cin c a1 y1++(.CCX y1 c c1::head1Post a y cin c a1 y1 c1 b'' bits y2 ys cs) := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt,xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,y3,ys,rfl⟩ : ∃ y0 y1 y2 y3 ys,dst=y0::y1::y2::y3::ys := by
    match dst, hd with
    | y0::y1::y2::y3::ys, _ => exact ⟨y0,y1,y2,y3,ys,rfl⟩
  obtain ⟨c,c1,c2,cs,hct⟩ : ∃ c c1 c2 cs,carry.take ((y0::y1::y2::y3::ys).length-1)=c::c1::c2::cs := by
    have hl : 3≤(carry.take ((y0::y1::y2::y3::ys).length-1)).length := by
      rw [List.length_take]; simp only [List.length_cons]; omega
    match carry.take ((y0::y1::y2::y3::ys).length-1), hl with
    | c::c1::c2::cs, _ => exact ⟨c,c1,c2,cs,rfl⟩
  obtain ⟨b'',b3,bits,e⟩ := diag_cons3 x0 x1 xt
  have hcm : ∀q∈c::c1::c2::cs,q∈carry := fun q h => List.mem_of_mem_take (hct ▸ h)
  refine ⟨x0,x1,y0,y1,y2,c,c1,b'',b3::bits,y3::ys,c2::cs,by simp,hcm c1 (by simp),?_,?_⟩
  · simp only [dAddZ2,e,hct,addHead1]
  · simp only [dAddZ,e,hct]; exact addHead0_split1 _ _ _ _ _ _ _ _ _ _ _ _

theorem dAddZ2_counts (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : 4≤carry.length) :
    toffoliCount (dAddZ2 xs dst carry cin)+1=toffoliCount (dAddZ xs dst carry cin) ∧
    measurementCount (dAddZ2 xs dst carry cin)=measurementCount (dAddZ xs dst carry cin) := by
  obtain ⟨a,a1,y,y1,y2,c,c1,b'',bits,ys,cs,-,-,e2,e1⟩ := dAddZ2_shape xs dst carry cin hx hd hc
  rw [e2,e1]
  have t1 : ∀ (u v : Wire) (p : Program),toffoliCount (.CX u v::p)=toffoliCount p := fun _ _ _ => rfl
  have t2 : ∀ (u v w : Wire) (p : Program),toffoliCount (.CCX u v w::p)=1+toffoliCount p := fun _ _ _ _ => rfl
  simp only [toffoliCount_append,measurementCount_append,t1,t2]
  exact ⟨by omega,rfl⟩

theorem addHead1_slots (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addHead1 bits ys carry cin)=Challenge.gateSlots (addHead0 bits ys carry cin) := by
  unfold addHead1
  split
  · rw [addHead0_split1]
    simp [Challenge.gateSlots_append,Challenge.gateSlots,Challenge.instructionSlots]
  · rfl

theorem dAddZ2_slots_eq (xs dst carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (dAddZ2 xs dst carry cin)=Challenge.gateSlots (dAddZ xs dst carry cin) :=
  addHead1_slots _ _ _ _

theorem y_mem_mappedMajority (b : MappedBit) (y cin t : Wire) : y∈wires (mappedMajority b y cin t) := by
  cases hw : b.wire <;> cases hf : b.flip <;>
    simp [mappedMajority,hw,hf,majority,borrowMajority,wires,Instr.wires]

theorem addHead1_wires_le (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (addHead1 bits ys carry cin)⊆wires (addHead0 bits ys carry cin) := by
  unfold addHead1
  split
  · rename_i a a1 b'' b3 bits' y y1 y2 y3 ys' c c1 c2 cs
    rw [addHead0_split1]
    have hy2 : y2∈wires (head1Post a y cin c a1 y1 c1 b'' (b3::bits') y2 (y3::ys') (c2::cs)) := by
      have h := y_mem_mappedMajority b'' y2 c1 c2
      simp only [head1Post,mappedAdd,wires_append,Finset.mem_union] at h ⊢
      tauto
    simp only [wires_append,wires,Instr.wires]
    apply Finset.union_subset_union (Finset.Subset.refl _)
    intro q hq
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hq ⊢
    rcases hq with (rfl|rfl)|h
    · exact Or.inr hy2
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr h
  · exact Finset.Subset.refl _

theorem dAddZ2_wires_le (xs dst carry : List Wire) (cin : Wire) :
    wires (dAddZ2 xs dst carry cin)⊆wires (dAddZ xs dst carry cin) :=
  addHead1_wires_le _ _ _ _

theorem dAddZ2_mem (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : 4≤carry.length) :
    ∀i∈dAddZ2 xs dst carry cin,i∈dAddZ xs dst carry cin ∨ ∃ y c,y∈dst ∧ c∈carry ∧ i=.CX y c := by
  obtain ⟨a,a1,y,y1,y2,c,c1,b'',bits,ys,cs,hy2,hc1,e2,e1⟩ := dAddZ2_shape xs dst carry cin hx hd hc
  rw [e2,e1]
  intro i hi
  simp only [List.mem_append,List.mem_cons] at hi ⊢
  rcases hi with hi|hi|hi
  · exact Or.inl (Or.inl hi)
  · exact Or.inr ⟨y2,c1,hy2,hc1,hi⟩
  · exact Or.inl (Or.inr (Or.inr hi))

theorem dAddZ2_wires (xs dst carry : List Wire) (cin : Wire) :
    wires (dAddZ2 xs dst carry cin)⊆wires (dAddZ xs dst carry cin)∪dst.toFinset∪carry.toFinset :=
  (dAddZ2_wires_le xs dst carry cin).trans
    (Finset.subset_union_left.trans Finset.subset_union_left)

theorem dAddZ2_physical (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : 4≤carry.length) (hdc : ∀q∈dst,q∉carry) (h : GatePhysical (dAddZ xs dst carry cin)) :
    GatePhysical (dAddZ2 xs dst carry cin) := by
  intro i hi
  rcases dAddZ2_mem xs dst carry cin hx hd hc i hi with h'|⟨y,c,hy,hcm,rfl⟩
  · exact h i h'
  · show y≠c
    intro e; exact hdc y hy (e ▸ hcm)

end ECDSAAdd.Entrant.DiagSq
end

namespace ECDSAAdd.Entrant.Z5Diagonal
open Arithmetic DiagSq KRegs

def clear (R : KRegs) : Program := R.c8g++(dAddZ2 R.lo R.dlo R.carry R.cin++
  dAddZ2 R.hi R.dhi R.carry R.cin++corrBackZ R++R.c7g++R.c6w++
  rawClearT R.S R.T R.pad R.carry++R.scl1591++rawClearT R.hi R.dhi R.pad R.carry++
  rawClearT R.lo R.dlo R.pad R.carry)

def makeC (R : KRegs) : Program := DiagSq.makeZ R++R.scl1591
def clearC (R : KRegs) : Program := R.smk++clear R

theorem clearSum_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (base : State) (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B 0 T) R.scl1591 := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hs := w.S
  have hl : R.hi.length=R.h := by omega
  have av := regValue_lt R.lo base.basis; have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hl] at bv
  have hS : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [show R.S.length=R.h+1 by omega,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) hS
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have r := R.scl1591_correct w hn t rec (by rw [sv,al,bl])
    ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
  have val : (regValue (reg R 2) (run R.scl1591 rec t).basis : Int) ≡ 0 [ZMOD (2^(reg R 2).length : Nat)] := by
    change (regValue R.S _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec2] using ht.step hn 2 0 r.1 r.2.2 val


theorem clear_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (clear R) m s).phase=s.phase ∧
    regValue R.dst (run (clear R) m s).basis=0 ∧
    regValue R.S (run (clear R) m s).basis=0 ∧
    regValue R.T (run (clear R) m s).basis=0 ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (clear R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let A := rawValue R.h a
  let B := rawValue R.h b
  let S := a+b
  let Z := rawValue (R.h+1) S
  let d : Int := ((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)-(2^(2*R.h-1) : Nat)
  have alo : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bhi : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have hA : A<2^R.dlo.length := by
    have v := rawValue_bound R.lo s.basis (by omega)
    simpa only [L0,L2] using v
  have hB : B<2^R.dhi.length := by
    have v := rawValue_bound R.hi s.basis (by omega)
    simpa only [hhi,L3,show 2*(R.bank.length-R.h)=2*R.h by omega] using v
  have slt : S<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [S]; omega
  have st1 := daddloZ2_transition R w he hn s hc0 hi0 (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat) (sq_sub_even a)
    (by push_cast; simp [a])
  have st1' : Transition R s (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (vec A (b^2 : Nat) S (2*a*b : Nat)) (dAddZ2 R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add] using st1
  have st2 := daddhiZ2_transition R w he hn s hc0 hi0 A (b^2 : Nat) S (2*a*b : Nat) (sq_sub_even b)
    (by push_cast; simp [b])
  have st2' : Transition R s (vec A (b^2 : Nat) S (2*a*b : Nat))
      (vec A B S (2*a*b : Nat)) (dAddZ2 R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add] using st2
  have st3 := corrBackZ_transition R w he hh hn s hz0 hc0 hi0 A B (2*a*b : Nat)
  have st4 := addhiZ_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d) hB (by
    apply dvd_add
    · push_cast; exact ⟨(a:Int)*b, by ring⟩
    · dsimp only [d]
      apply dvd_sub
      · apply Dvd.dvd.mul_right
        push_cast; exact dvd_pow_self 2 (by omega)
      · push_cast; exact dvd_pow_self 2 (by omega))
  have norm := cross_normalize R.h a b hh alo bhi
  have norm' : ((2*a*b : Nat) : Int)+d+B+A=Z := by
    change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
      (2*a*b : Nat) at norm
    dsimp only [d]
    linarith only [norm]
  have bnd := KRegs.raw_low_bound R.h a b (by omega) alo bhi
  have hT1 : R.T.length=2*R.h+2 := by have := w.T; have := w.S; omega
  have zlt : Z<2^(2*R.h+2) := by
    have x := KRegs.raw_lo_le (R.h+1) S (by omega) (by rw [pow_succ]; dsimp only [S]; omega)
    rw [show 2*(R.h+1)=2*R.h+2 by ring] at x
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (by positivity)) x
  have p2 : 2^(2*R.h)≤2^(2*R.h+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb1 : A≤Z%2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact bnd.1
  have hA1 : A<2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact lt_of_lt_of_le bnd.2 p2
  have hZ1 : Z<2^R.T.length := by rw [hT1]; exact zlt
  have st5 := addloW_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d+B) Z hA (rawValue_even _ _ (by omega)) norm' hZ1 hb1 hA1
  rw [norm'] at st5
  have st6 := rawclearSum_transitionT R w hn s hp0 hc0 A B S slt
  rw [hSS] at st6
  have st7 := clearSum_transition R w he hn s hz0 hc0 hi0 A B 0
  have st8 := rawclearhi_transitionT R w he hn s hp0 hc0 A 0 0
  have st9 := rawclearlo_transitionT R w he hn s hp0 hc0 0 0 0
  have st3' : Transition R s (vec A B S (2*a*b : Nat))
      (vec A B S ((2*a*b : Nat)+d)) (corrBackZ R) := by
    (convert st3 using 1; try rfl)
    simp only [d]
    congr 1
    ring
  have tail := ((((((((st1'.seq st2').seq st3').seq st4).seq st5).seq st6).seq st7).seq st8).seq st9)
  have initial := clearZ_start_shape R w he hn s (m.take (measurementCount R.c8g)) hd0 hS0 hT0 hz0 hc0 hi0
  have result := tail _ (m.drop (measurementCount R.c8g)) initial
  have final : Shape R s (run (clear R) m s) (vec 0 0 0 0) := by
    simpa only [clear,run_append] using result
  refine ⟨final.phase,?_,final.exact 2 0 rfl (by norm_num),final.exact 3 0 rfl (by norm_num),final.rest⟩
  have zlo : regValue R.dlo (run (clear R) m s).basis=0 := final.exact 0 0 rfl (by norm_num)
  have zhi : regValue R.dhi (run (clear R) m s).basis=0 := final.exact 1 0 rfl (by norm_num)
  rw [R.dst_value w,zlo,zhi]
  simp

variable (R : KRegs)

theorem diag_sq_full_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.makeZ R) R.invF := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  have r := DiagSq.makeZ_correct R w he hh hn s m hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [invF,r.2.2.1,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  exact ⟨rfl,rfl⟩

theorem diag_sq_full_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (clear R) R.invF := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  have r := clear_correct R w he hh hn s m hd0 (by rw [hI.1,R.lo_mod w,R.hi_div w]) (by rw [hI.2,R.lo_mod w,R.hi_div w])
    (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [regValue_append,r.2.2.1,r.2.2.2.1]; simp

theorem diag_sq_cl_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (makeC R) R.invC := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  let a := m.take (measurementCount (DiagSq.makeZ R))
  let b := m.drop (measurementCount (DiagSq.makeZ R))
  have r := DiagSq.makeZ_correct R w he hh hn s a hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  generalize hu : run (DiagSq.makeZ R) a s=u at r
  have fu : ∀q,q∉R.S → q∉R.T → q∉R.dst → u.basis q=s.basis q := fun q a b c => r.2.2.2.2 q c a b
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S ∧ q∉R.T ∧ q∉R.dst) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => fu q (hl q hq).1 (hl q hq).2.1 (hl q hq).2.2)
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) : q∉R.S ∧ q∉R.T ∧ q∉R.dst :=
    let x := R.outside hn q h; ⟨x.2.1,x.2.2,x.1⟩
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := R.scl1591_correct w hn u b (by rw [r.2.2.1,lo,hi])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((fu _ (o _ (by simp)).1 (o _ (by simp)).2.1 (o _ (by simp)).2.2).trans hi0)
  have eq : run (makeC R) m s=run R.scl1591 b u := by
    rw [makeC,run_append,←hu]
  rw [eq]
  have sT := R.outside hn
  have dS : ∀q∈R.dst,q∉R.S := kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega)
  have TS : ∀q∈R.T,q∉R.S := kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega)
  refine ⟨c.1.trans r.1,?_,?_,?_⟩
  · rw [kkeep c.2.2 dS,r.2.1]
  · refine ⟨c.2.1,?_⟩
    rw [kkeep c.2.2 TS,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2 q xS).trans (fu q xS xT h)

theorem diag_sq_cl_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (clearC R) R.invC := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  let a := m.take (measurementCount R.smk)
  let b := m.drop (measurementCount R.smk)
  have r := R.smk_correct w hn s a hI.1 (xz hz0 hz) hc0 hi0
  generalize hu : run R.smk a s=u at r
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin ∨ q∈R.dst ∨ q∈R.T) : q∉R.S := by
    rcases h with h|h|h|h|h|h|h
    · exact (R.outside hn q (Or.inl h)).2.1
    · exact (R.outside hn q (Or.inr (Or.inl h))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inl h)))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inr (Or.inl h))))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inr (Or.inr h))))).2.1
    · exact kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega) q h
    · exact kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega) q h
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => r.2.2 q (hl q hq))
  have bk := keep R.bank (fun q h => o q (Or.inl h))
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := clear_correct R w he hh hn u b (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),bk]; exact hd0)
    (by rw [r.2.1,lo,hi])
    (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))),hI.2,lo,hi,R.lo_mod w,R.hi_div w])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inl h))))).trans hp0)
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((r.2.2 _ (o _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).trans hi0)
  have eq : run (clearC R) m s=run (clear R) b u := by
    rw [clearC,run_append,←hu]
  rw [eq]
  refine ⟨c.1.trans r.1,c.2.1,?_,?_⟩
  · rw [regValue_append,c.2.2.1,c.2.2.2.1]; simp
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2.2.2 q h xS xT).trans (r.2.2 q xS)


theorem clear_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (clear R)+(R.bank.length-R.h)+12+DiagSq.parR R=toffoliCount (DiagSq.clear R) ∧
    measurementCount (clear R)+4+DiagSq.parR R=measurementCount (DiagSq.clear R) := by
  have a := R.piece_counts w
  have b := R.scl1591_counts w
  have z8 := R.c8g_counts w; have z7 := R.c7g_counts w; have z6 := R.c6w_counts w
  have cb := DiagSq.corrBackZ_counts R w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hdl := w.dst; have hpl := w.pad; have hh := w.hh; have h5 := w.h5
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have r1 := DiagSq.rawClearT_counts R.lo R.dlo R.pad R.carry (by omega) (by omega) hpl (by omega)
  have r2 := DiagSq.rawClearT_counts R.hi R.dhi R.pad R.carry (by omega) (by omega) hpl (by omega)
  have r5 := DiagSq.rawClearT_counts R.S R.T R.pad R.carry (by omega) (by omega) hpl (by omega)
  have da1 := DiagSq.dAddZ_counts R.lo R.dlo R.carry R.cin (by omega) (by omega) (by omega)
  have da2 := DiagSq.dAddZ_counts R.hi R.dhi R.carry R.cin (by omega) (by omega) (by omega)
  have db1 := DiagSq.dAddZ2_counts R.lo R.dlo R.carry R.cin (by omega) (by omega) (by omega)
  have db2 := DiagSq.dAddZ2_counts R.hi R.dhi R.carry R.cin (by omega) (by omega) (by omega)
  simp only [clear,DiagSq.clear,toffoliCount_append,measurementCount_append,DiagSq.parR]
  constructor <;> omega

theorem makeC_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (makeC R)+(R.bank.length-R.h)+11+DiagSq.parR R=toffoliCount (DiagSq.makeC R) ∧
    measurementCount (makeC R)+4+DiagSq.parR R=measurementCount (DiagSq.makeC R) := by
  have a := R.piece_counts w
  have b := R.scl1591_counts w
  have z := DiagSq.makeZ_counts_rel R w
  simp only [makeC,DiagSq.makeC,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem clearC_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (clearC R)+(R.bank.length-R.h)+12+DiagSq.parR R=toffoliCount (DiagSq.clearC R) ∧
    measurementCount (clearC R)+4+DiagSq.parR R=measurementCount (DiagSq.clearC R) := by
  have h := clear_counts_diff R w
  simp only [clearC,DiagSq.clearC,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem clear_support (R : KRegs) (w : R.W) : wires (clear R)⊆R.all.toFinset := by
  have old := (DiagSq.steps_support R w).2
  have new := R.scl1591_support w
  have pcs := R.piece_support w
  have q2 := pcs.2.2.2.1
  simp only [wires_append,Finset.union_subset_iff] at q2
  have c8w : wires R.c8g⊆R.all.toFinset := R.c8g_wires.trans q2.1.1
  have c7w : wires R.c7g⊆R.all.toFinset := R.c7g_wires.trans q2.1.2
  have c6w' : wires R.c6w⊆R.all.toFinset := R.c6w_wires.trans q2.2
  clear q2 pcs
  simp only [clear,DiagSq.clear,wires_append,Finset.union_subset_iff] at old ⊢
  have rS : wires (rawClearT R.S R.T R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have rH : wires (rawClearT R.hi R.dhi R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have rL : wires (rawClearT R.lo R.dlo R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have cbw : wires (corrBackZ R)⊆R.all.toFinset := (DiagSq.wires_of_mem (DiagSq.corrBackZ_mem R)).trans (by tauto)
  have daw1 : wires (dAddZ R.lo R.dlo R.carry R.cin)⊆R.all.toFinset := (DiagSq.wires_of_mem (DiagSq.dAddZ_mem _ _ _ _)).trans (by tauto)
  have daw2 : wires (dAddZ R.hi R.dhi R.carry R.cin)⊆R.all.toFinset := (DiagSq.wires_of_mem (DiagSq.dAddZ_mem _ _ _ _)).trans (by tauto)
  have dbw1 : wires (dAddZ2 R.lo R.dlo R.carry R.cin)⊆R.all.toFinset :=
    (DiagSq.dAddZ2_wires_le _ _ _ _).trans daw1
  have dbw2 : wires (dAddZ2 R.hi R.dhi R.carry R.cin)⊆R.all.toFinset :=
    (DiagSq.dAddZ2_wires_le _ _ _ _).trans daw2
  tauto

theorem makeC_support (R : KRegs) (w : R.W) : wires (makeC R)⊆R.all.toFinset := by
  simpa only [makeC,wires_append,Finset.union_subset_iff] using
    And.intro (DiagSq.makeZ_support R w) (R.scl1591_support w)

theorem clearC_support (R : KRegs) (w : R.W) : wires (clearC R)⊆R.all.toFinset := by
  simpa only [clearC,wires_append,Finset.union_subset_iff] using
    And.intro (R.piece_support w).1 (clear_support R w)

theorem clear_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (clear R) := by
  have old := (DiagSq.steps_physical R w hn).2
  have new := R.scl1591_physical w hn
  have z8 := R.c8g_physical hn; have z7 := R.c7g_physical hn; have z6 := R.c6w_physical hn
  have oldm := (DiagSq.steps_physical R w hn).1
  simp only [DiagSq.make,DiagSq.headBlock,DiagSq.seeds,gatePhysical_append] at oldm
  simp only [clear,DiagSq.clear,gatePhysical_append] at old ⊢
  have rS := DiagSq.rawClearT_physical_of R.S R.T R.pad R.carry (by tauto) (by tauto)
  have rH := DiagSq.rawClearT_physical_of R.hi R.dhi R.pad R.carry (by tauto) (by tauto)
  have rL := DiagSq.rawClearT_physical_of R.lo R.dlo R.pad R.carry (by tauto) (by tauto)
  have cbp : GatePhysical (corrBackZ R) := fun i hi => (show GatePhysical (corrBack R) by tauto) i (DiagSq.corrBackZ_mem R i hi)
  have dap1 : GatePhysical (dAddZ R.lo R.dlo R.carry R.cin) := fun i hi => (show GatePhysical (mappedDiagAdd R.lo R.dlo R.carry R.cin) by tauto) i (DiagSq.dAddZ_mem _ _ _ _ i hi)
  have dap2 : GatePhysical (dAddZ R.hi R.dhi R.carry R.cin) := fun i hi => (show GatePhysical (mappedDiagAdd R.hi R.dhi R.carry R.cin) by tauto) i (DiagSq.dAddZ_mem _ _ _ _ i hi)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have he5 := w.h5; have hh := w.hh
  have dc : ∀q∈R.dst,q∉R.carry := kdis hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have dbp1 : GatePhysical (dAddZ2 R.lo R.dlo R.carry R.cin) :=
    DiagSq.dAddZ2_physical _ _ _ _ (by omega) (by omega) (by omega) (fun q h => dc q (List.mem_of_mem_take h)) dap1
  have dbp2 : GatePhysical (dAddZ2 R.hi R.dhi R.carry R.cin) :=
    DiagSq.dAddZ2_physical _ _ _ _ (by omega) (by omega) (by omega) (fun q h => dc q (List.mem_of_mem_drop h)) dap2
  tauto

theorem makeC_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeC R) := by
  simpa only [makeC,gatePhysical_append] using
    And.intro (DiagSq.makeZ_physical R w hn) (R.scl1591_physical w hn)

theorem clearC_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (clearC R) := by
  simpa only [clearC,gatePhysical_append] using
    And.intro (R.piece_physical hn).1 (clear_physical R w hn)

theorem clear_slots_le (R : KRegs) : Challenge.gateSlots (clear R)≤Challenge.gateSlots (DiagSq.clear R) := by
  have h := R.scl1591_slots
  have z8 := R.c8g_slots; have z7 := R.c7g_slots; have z6 := R.c6w_slots
  have rS := DiagSq.rawClearT_slots_le R.S R.T R.pad R.carry
  have rH := DiagSq.rawClearT_slots_le R.hi R.dhi R.pad R.carry
  have rL := DiagSq.rawClearT_slots_le R.lo R.dlo R.pad R.carry
  have cb := DiagSq.corrBackZ_slots R
  have da1 := DiagSq.dAddZ_slots R.lo R.dlo R.carry R.cin; have da2 := DiagSq.dAddZ_slots R.hi R.dhi R.carry R.cin
  have db1 := DiagSq.dAddZ2_slots_eq R.lo R.dlo R.carry R.cin; have db2 := DiagSq.dAddZ2_slots_eq R.hi R.dhi R.carry R.cin
  simp only [clear,DiagSq.clear,Challenge.gateSlots_append] at *
  omega

theorem makeC_slots_le (R : KRegs) : Challenge.gateSlots (makeC R)≤Challenge.gateSlots (DiagSq.makeC R) := by
  have h := R.scl1591_slots
  have z := DiagSq.makeZ_slots R
  simp only [makeC,DiagSq.makeC,Challenge.gateSlots_append] at *
  omega

theorem clearC_slots_le (R : KRegs) : Challenge.gateSlots (clearC R)≤Challenge.gateSlots (DiagSq.clearC R) := by
  have h := clear_slots_le R
  simp only [clearC,DiagSq.clearC,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.Z5Diagonal

namespace ECDSAAdd.Entrant.Z5Diagonal
open Arithmetic

theorem clear_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (clear R)=DiagSq.cost R-R.h-12-DiagSq.parR R ∧ measurementCount (clear R)+4+DiagSq.parR R=DiagSq.cost R := by
  have a := clear_counts_diff R w
  have b := DiagSq.clear_counts R w he
  constructor <;> omega

theorem steps_support (R : KRegs) (w : R.W) :
    wires (DiagSq.makeZ R)⊆R.all.toFinset ∧ wires (clear R)⊆R.all.toFinset :=
  ⟨DiagSq.makeZ_support R w,clear_support R w⟩

theorem steps_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (DiagSq.makeZ R) ∧ GatePhysical (clear R) :=
  ⟨DiagSq.makeZ_physical R w hn,clear_physical R w hn⟩

theorem tiny_slots (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (DiagSq.makeZ R)≤150800 ∧ Challenge.gateSlots (clear R)≤150800 :=
  ⟨(DiagSq.makeZ_slots R).trans (DiagSq.tiny_slots R w he hh).1,(clear_slots_le R).trans (DiagSq.tiny_slots R w he hh).2⟩

end ECDSAAdd.Entrant.Z5Diagonal
end

section
namespace ECDSAAdd.Entrant.TrimSquare3
open Arithmetic
theorem tsq3_slots_rel (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsq3 xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsq2 xs dst pad carry cin) ∧
    Challenge.gateSlots (tsqc3 xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsqc2 xs dst pad carry cin) := by
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨le_refl _,le_refl _⟩
  · rw [e1,e2,e3,e4]
    have d := addDrop_slots x y cy c
    simp only [Challenge.gateSlots_append]
    constructor <;> omega
theorem tsqM_slots_rel (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (TrimMid.tsqM xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsq2 xs dst pad carry cin) ∧
    Challenge.gateSlots (TrimMid.tsqcM xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsqc2 xs dst pad carry cin) :=
  ⟨(TrimMid.tsqM_rel xs dst pad carry cin).1.2.1.trans (tsq3_slots_rel xs dst pad carry cin).1,
    (TrimMid.tsqM_rel xs dst pad carry cin).2.2.1.trans (tsq3_slots_rel xs dst pad carry cin).2⟩
end ECDSAAdd.Entrant.TrimSquare3
end

section
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TrimSquare4
set_option linter.unusedVariables false
open Arithmetic

/-! Bit 1 of `TrimSquare.drop2` in the square clear `tsqc3`. At the start of `tsqc3` the destination holds
exactly `X²` and the carries are clean. `drop2` copies the dead bit-0 carry (`CX x₀ c`), and the bit-1
majority then fires on `(y₁ ⊕ x₁) ∧ (x₀ ⊕ x₁) = x₁ ∧ ¬x₀ = y₂` (bits of a square), so its Toffoli is
the CNOT `y₂ → c₁`. -/

def d3Pre (a c a1 y1 : Wire) : Program := [.CX a c,.CX a1 y1,.CX a1 c]

def d3Post (a y cin c a1 y1 c1 : Wire) (b'' : MappedBit) (bits : List MappedBit)
    (y2 : Wire) (ys cs : List Wire) : Program :=
  ([.CX a1 c1,.CX a1 c,.CX a1 y1]++(mappedAdd (b''::bits) (y2::ys) cs c1++mappedEraseCarry ⟨some a1,false⟩ y1 c c1++
    mappedSum ⟨some a1,false⟩ y1 c))++[.CX a c]++mappedSum ⟨some a,false⟩ y cin

def drop3 (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
  match bits, ys, carry with
  | ⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits', y::y1::y2::y3::ys', c::c1::c2::cs =>
      d3Pre a c a1 y1++(.CX y2 c1::d3Post a y cin c a1 y1 c1 b'' (b3::bits') y2 (y3::ys') (c2::cs))
  | bits, ys, carry => TrimSquare.drop2 bits ys carry cin

theorem drop2_split1 (a y cin c a1 y1 c1 : Wire) (b'' : MappedBit) (bits : List MappedBit)
    (y2 : Wire) (ys cs : List Wire) :
    TrimSquare.drop2 (⟨some a,false⟩::⟨some a1,false⟩::b''::bits) (y::y1::y2::ys) (c::c1::cs) cin=
      d3Pre a c a1 y1++(.CCX y1 c c1::d3Post a y cin c a1 y1 c1 b'' bits y2 ys cs) := by
  simp [TrimSquare.drop2,mappedAdd,mappedMajority,majority,d3Pre,d3Post,List.append_assoc]

theorem drop3_run (a a1 y y1 y2 y3 c c1 c2 cin : Wire) (b'' b3 : MappedBit) (bits : List MappedBit)
    (ys cs : List Wire) (m : List Bool) (s : State)
    (hd : [a,a1,y1,y2,c].Nodup)
    (hcopy : ((s.basis y1 ^^ s.basis a1) && (s.basis c ^^ s.basis a ^^ s.basis a1))=s.basis y2) :
    run (drop3 (⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits) (y::y1::y2::y3::ys) (c::c1::c2::cs) cin) m s=
      run (TrimSquare.drop2 (⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits) (y::y1::y2::y3::ys) (c::c1::c2::cs) cin) m s := by
  rw [drop2_split1]
  simp only [drop3]
  have m0 : measurementCount (d3Pre a c a1 y1)=0 := rfl
  rw [run_append,run_append,m0,List.take_zero,List.drop_zero]
  symm
  apply DiagSq.ccx_as_cx
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,or_false,
    not_false_eq_true,and_true] at hd
  obtain ⟨⟨h1,h2,h3,h4⟩,⟨h5,h6,h7⟩,⟨h8,h9⟩,h10⟩ := hd
  simp only [d3Pre,run,writeBit,Function.update]
  simp [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm h5,
    Ne.symm h6,Ne.symm h7,Ne.symm h8,Ne.symm h9,Ne.symm h10] at hcopy ⊢
  try (rw [← hcopy])

def tsqc4 (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++signedSquareTop xs dst++
    TrimSquare3.rowsClear3 xs dst pad carry

theorem drop3_shape (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : dst.length-1≤carry.length) :
    ∃ x0 x1 xt y0 y1 y2 y3 ys c c1 c2 cs b'' b3 bits,xs=x0::x1::xt ∧ dst=y0::y1::y2::y3::ys ∧
      carry.take (dst.length-1)=c::c1::c2::cs ∧
      mappedDiagonal xs=⟨some x0,false⟩::⟨some x1,false⟩::b''::b3::bits := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt,xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,y3,ys,rfl⟩ : ∃ y0 y1 y2 y3 ys,dst=y0::y1::y2::y3::ys := by
    match dst, hd with
    | y0::y1::y2::y3::ys, _ => exact ⟨y0,y1,y2,y3,ys,rfl⟩
  obtain ⟨c,c1,c2,cs,hct⟩ : ∃ c c1 c2 cs,carry.take ((y0::y1::y2::y3::ys).length-1)=c::c1::c2::cs := by
    have hl : 3≤(carry.take ((y0::y1::y2::y3::ys).length-1)).length := by
      rw [List.length_take]; simp only [List.length_cons] at hc ⊢; omega
    match carry.take ((y0::y1::y2::y3::ys).length-1), hl with
    | c::c1::c2::cs, _ => exact ⟨c,c1,c2,cs,rfl⟩
  obtain ⟨b'',b3,bits,e⟩ := DiagSq.diag_cons3 x0 x1 xt
  exact ⟨x0,x1,xt,y0,y1,y2,y3,ys,c,c1,c2,cs,b'',b3,bits,rfl,rfl,hct,e⟩

theorem drop3_eq (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : dst.length-1≤carry.length) :
    ∃ a a1 y y1 y2 c c1 b'' bits ys cs,y2∈dst ∧ c1∈carry ∧
      drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin=
        d3Pre a c a1 y1++(.CX y2 c1::d3Post a y cin c a1 y1 c1 b'' bits y2 ys cs) ∧
      TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin=
        d3Pre a c a1 y1++(.CCX y1 c c1::d3Post a y cin c a1 y1 c1 b'' bits y2 ys cs) := by
  obtain ⟨x0,x1,xt,y0,y1,y2,y3,ys,c,c1,c2,cs,b'',b3,bits,rfl,rfl,hct,e⟩ := drop3_shape xs dst carry cin hx hd hc
  have hcm : ∀q∈c::c1::c2::cs,q∈carry := fun q h => List.mem_of_mem_take (hct ▸ h)
  refine ⟨x0,x1,y0,y1,y2,c,c1,b'',b3::bits,y3::ys,c2::cs,by simp,hcm c1 (by simp),?_,?_⟩
  · rw [e,hct]; rfl
  · rw [e,hct]; exact drop2_split1 _ _ _ _ _ _ _ _ _ _ _ _

theorem drop3_counts (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : dst.length-1≤carry.length) :
    toffoliCount (drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin)+1=
      toffoliCount (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin) ∧
    measurementCount (drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin)=
      measurementCount (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin) := by
  obtain ⟨a,a1,y,y1,y2,c,c1,b'',bits,ys,cs,-,-,e2,e1⟩ := drop3_eq xs dst carry cin hx hd hc
  rw [e2,e1]
  have t1 : ∀ (u v : Wire) (p : Program),toffoliCount (.CX u v::p)=toffoliCount p := fun _ _ _ => rfl
  have t2 : ∀ (u v w : Wire) (p : Program),toffoliCount (.CCX u v w::p)=1+toffoliCount p := fun _ _ _ _ => rfl
  simp only [toffoliCount_append,measurementCount_append,t1,t2]
  exact ⟨by omega,rfl⟩

theorem drop3_slots (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (drop3 bits ys carry cin)=Challenge.gateSlots (TrimSquare.drop2 bits ys carry cin) := by
  unfold drop3
  split
  · rw [drop2_split1]
    simp [Challenge.gateSlots_append,Challenge.gateSlots,Challenge.instructionSlots]
  · rfl

theorem drop3_wires_le (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (drop3 bits ys carry cin)⊆wires (TrimSquare.drop2 bits ys carry cin) := by
  unfold drop3
  split
  · rename_i a a1 b'' b3 bits' y y1 y2 y3 ys' c c1 c2 cs
    rw [drop2_split1]
    have hy2 : y2∈wires (d3Post a y cin c a1 y1 c1 b'' (b3::bits') y2 (y3::ys') (c2::cs)) := by
      have h := DiagSq.y_mem_mappedMajority b'' y2 c1 c2
      simp only [d3Post,mappedAdd,wires_append,Finset.mem_union] at h ⊢
      tauto
    simp only [wires_append,wires,Instr.wires]
    apply Finset.union_subset_union (Finset.Subset.refl _)
    intro q hq
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hq ⊢
    rcases hq with (rfl|rfl)|h
    · exact Or.inr hy2
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr h
  · exact Finset.Subset.refl _

theorem drop3_physical (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) (hdc : ∀q∈ys,q∉carry)
    (h : GatePhysical (TrimSquare.drop2 bits ys carry cin)) :
    GatePhysical (drop3 bits ys carry cin) := by
  unfold drop3
  split
  · rename_i a a1 b'' b3 bits' y y1 y2 y3 ys' c c1 c2 cs
    rw [drop2_split1] at h
    intro i hi
    simp only [List.mem_append,List.mem_cons] at hi
    rcases hi with hi|hi|hi
    · exact h i (List.mem_append_left _ hi)
    · subst hi
      show y2≠c1
      intro e; exact hdc y2 (by simp) (by rw [e]; simp)
    · exact h i (List.mem_append_right _ (List.mem_cons_of_mem _ hi))
  · exact h

/-- `drop3` runs exactly like `drop2`, followed by any program, from a state whose destination holds
the square and whose carries are clean. -/
theorem drop3_prefix_run (cin : Wire) (xs dst pad carry : List Wire) (T : Program)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hc0 : regValue carry s.basis=0) :
    run (drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++T) records s=
      run (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++T) records s := by
  obtain ⟨x0,x1,xt,y0,y1,y2,y3,ys,c,c1,c2,cs,b'',b3,bits,rfl,rfl,hct,e⟩ :=
    drop3_shape xs dst carry cin hx (by omega) hc
  have mc := (drop3_counts (x0::x1::xt) (y0::y1::y2::y3::ys) carry cin hx
    (by simp only [List.length_cons] at hd ⊢; omega) hc).2
  have hcm : ∀q∈c::c1::c2::cs,q∈carry := fun q h => List.mem_of_mem_take (hct ▸ h)
  rw [run_append,run_append (TrimSquare.drop2 _ _ _ _),mc]
  congr 1
  rw [e,hct]
  have cnt := fun w => List.nodup_iff_count.mp hn w
  have cpos := fun w (h : w∈carry) => List.count_pos_iff.mpr h
  have nd : [x0,x1,y1,y2,c].Nodup := by
    have s1 : [x0,x1].Sublist (cin::x0::x1::xt) := (List.sublist_append_left [x0,x1] xt).cons cin
    have s2 : [y1,y2].Sublist (y0::y1::y2::y3::ys) := (List.sublist_append_left [y1,y2] (y3::ys)).cons y0
    have s3 : [c].Sublist carry := List.singleton_sublist.mpr (hcm c (by simp))
    apply List.nodup_iff_count.mpr; intro w
    have h := cnt w
    have t1 := s1.count_le w; have t2 := s2.count_le w; have t3 := s3.count_le w
    have e : [x0,x1,y1,y2,c].count w=[x0,x1].count w+[y1,y2].count w+[c].count w := by
      simp only [List.count_cons,List.count_nil]; omega
    simp only [List.count_append] at h
    omega
  apply drop3_run x0 x1 y0 y1 y2 y3 c c1 c2 cin b'' b3 bits ys cs _ s nd
  have cz : s.basis c=false := (regValue_zero _ _).mp hc0 c (hcm c (by simp))
  rw [cz,Bool.false_xor]
  apply DiagSq.bits_of_sq8 y0 y1 y2 x0 x1 (y3::ys) xt s.basis ((regValue (y0::y1::y2::y3::ys) s.basis : Nat) : Int)
    (Int.ModEq.refl _)
  rw [hval]; push_cast; simp

theorem tsqc4_run (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hc0 : regValue carry s.basis=0) :
    run (tsqc4 xs dst pad carry cin) records s=run (TrimSquare3.tsqc3 xs dst pad carry cin) records s := by
  unfold tsqc4 TrimSquare3.tsqc3
  rw [List.append_assoc,List.append_assoc]
  exact drop3_prefix_run cin xs dst pad carry _ hn hx hd hc s records hval hc0

theorem tsqc4_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (tsqc4 xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (tsqc4 xs dst pad carry cin) records s).basis=0 ∧
    ∀q,q∉dst → (run (tsqc4 xs dst pad carry cin) records s).basis q=s.basis q := by
  rw [tsqc4_run cin xs dst pad carry hn hx hd hc s records hval hc0]
  exact TrimSquare3.tsqc3_correct cin xs dst pad carry hn hx hd hp hc s records hval hp0 hc0 hi0

theorem tsqc4_counts (xs dst pad carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    toffoliCount (tsqc4 xs dst pad carry cin)+1=toffoliCount (TrimSquare3.tsqc3 xs dst pad carry cin) ∧
    measurementCount (tsqc4 xs dst pad carry cin)=measurementCount (TrimSquare3.tsqc3 xs dst pad carry cin) := by
  have d := drop3_counts xs dst carry cin hx (by omega) hc
  unfold tsqc4 TrimSquare3.tsqc3
  simp only [toffoliCount_append,measurementCount_append]
  omega

theorem tsqc4_slots (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsqc4 xs dst pad carry cin)=Challenge.gateSlots (TrimSquare3.tsqc3 xs dst pad carry cin) := by
  unfold tsqc4 TrimSquare3.tsqc3
  simp only [Challenge.gateSlots_append,drop3_slots]

theorem tsqc4_wires_le (xs dst pad carry : List Wire) (cin : Wire) :
    wires (tsqc4 xs dst pad carry cin)⊆wires (TrimSquare3.tsqc3 xs dst pad carry cin) := by
  unfold tsqc4 TrimSquare3.tsqc3
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (drop3_wires_le _ _ _ _) (subset_refl _)) (subset_refl _)

theorem tsqc4_physical (xs dst pad carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup)
    (h : GatePhysical (TrimSquare3.tsqc3 xs dst pad carry cin)) :
    GatePhysical (tsqc4 xs dst pad carry cin) := by
  have hdc : ∀q∈dst,q∉carry.take (dst.length-1) := by
    intro q h1 h2
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr h1
    have b := List.count_pos_iff.mpr (List.mem_of_mem_take h2)
    simp only [List.count_cons,List.count_append] at h; omega
  unfold tsqc4 TrimSquare3.tsqc3 at *
  simp only [gatePhysical_append] at h ⊢
  exact ⟨⟨drop3_physical _ _ _ _ hdc h.1.1,h.1.2⟩,h.2⟩

/-! The same trim inside lane B's parity-adaptive clear `TrimMid.tsqcM`, which starts with the
same `drop2` in both branches. -/

def tsqcM4 (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  if TrimMid.oddLeaf xs.length then
    drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++TrimMid.clM (xs.length/2-1) xs dst pad carry
  else tsqc4 xs dst pad carry cin

theorem tsqcM4_run (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hc0 : regValue carry s.basis=0) :
    run (tsqcM4 xs dst pad carry cin) records s=run (TrimMid.tsqcM xs dst pad carry cin) records s := by
  unfold tsqcM4 TrimMid.tsqcM
  split_ifs
  · exact drop3_prefix_run cin xs dst pad carry _ hn hx hd hc s records hval hc0
  · exact tsqc4_run cin xs dst pad carry hn hx hd hc s records hval hc0

theorem tsqcM4_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (tsqcM4 xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (tsqcM4 xs dst pad carry cin) records s).basis=0 ∧
    ∀q,q∉dst → (run (tsqcM4 xs dst pad carry cin) records s).basis q=s.basis q := by
  rw [tsqcM4_run cin xs dst pad carry hn hx hd hc s records hval hc0]
  exact TrimMid.tsqcM_correct cin xs dst pad carry hn hx hd hp hc s records hval hp0 hc0 hi0

theorem tsqcM4_counts (xs dst pad carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    toffoliCount (tsqcM4 xs dst pad carry cin)+1=toffoliCount (TrimMid.tsqcM xs dst pad carry cin) ∧
    measurementCount (tsqcM4 xs dst pad carry cin)=measurementCount (TrimMid.tsqcM xs dst pad carry cin) := by
  unfold tsqcM4 TrimMid.tsqcM
  split_ifs
  · have d := drop3_counts xs dst carry cin hx (by omega) hc
    simp only [toffoliCount_append,measurementCount_append]
    omega
  · exact tsqc4_counts xs dst pad carry cin hx hd hp hc

theorem tsqcM4_slots (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsqcM4 xs dst pad carry cin)=Challenge.gateSlots (TrimMid.tsqcM xs dst pad carry cin) := by
  unfold tsqcM4 TrimMid.tsqcM
  split_ifs
  · simp only [Challenge.gateSlots_append,drop3_slots]
  · exact tsqc4_slots xs dst pad carry cin

theorem tsqcM4_wires_le (xs dst pad carry : List Wire) (cin : Wire) :
    wires (tsqcM4 xs dst pad carry cin)⊆wires (TrimMid.tsqcM xs dst pad carry cin) := by
  unfold tsqcM4 TrimMid.tsqcM
  split_ifs
  · simp only [wires_append]
    exact Finset.union_subset_union (drop3_wires_le _ _ _ _) (subset_refl _)
  · exact tsqc4_wires_le xs dst pad carry cin

theorem tsqcM4_physical (xs dst pad carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup)
    (h : GatePhysical (TrimMid.tsqcM xs dst pad carry cin)) :
    GatePhysical (tsqcM4 xs dst pad carry cin) := by
  unfold tsqcM4 TrimMid.tsqcM at *
  split_ifs at h ⊢
  · have hdc : ∀q∈dst,q∉carry.take (dst.length-1) := by
      intro q h1 h2
      have h := List.nodup_iff_count.mp hn q
      have a := List.count_pos_iff.mpr h1
      have b := List.count_pos_iff.mpr (List.mem_of_mem_take h2)
      simp only [List.count_cons,List.count_append] at h; omega
    simp only [gatePhysical_append] at h ⊢
    exact ⟨drop3_physical _ _ _ _ hdc h.1,h.2⟩
  · exact tsqc4_physical xs dst pad carry cin hn h

end ECDSAAdd.Entrant.TrimSquare4
end

section

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic
theorem sq_plain3_make (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqMake xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare3.tsq3 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare3.tsq3_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,trivial,fun q h _ => r.2.2 q h⟩
theorem sq_plain3_clear (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqClear xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare3.tsqc3 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare3.tsqc3_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,rfl,fun q h _ => r.2.2 q h⟩
theorem sq_mid4_clear (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqClear xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare4.tsqcM4 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare4.tsqcM4_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,rfl,fun q h _ => r.2.2 q h⟩
end ECDSAAdd.Entrant.LowZero18LowK

end


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end
