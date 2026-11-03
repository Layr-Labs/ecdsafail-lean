import ECDSAAdd.Submission.Entrant.MainPart02

set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.LowZero18Core =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18KRegs
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591LowK

/-! LowZero changes only the final inner addition and four outer additions.
The old raw leaves and the checked675 sum cleanup remain in use. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.LowZero18Diagonal
open Arithmetic DiagSq

def make (R : KRegs) : Program := DiagSq.makeZ R
def makeC (R : KRegs) : Program := make R++R.scl1591
abbrev clear := Z5Diagonal.clear
abbrev clearC := Z5Diagonal.clearC

theorem make_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (make R) m s).phase=s.phase ∧
    regValue R.dst (run (make R) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.S (run (make R) m s).basis=regValue R.lo s.basis+regValue R.hi s.basis ∧
    regValue R.T (run (make R) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (make R) m s).basis q=s.basis q :=
  DiagSq.makeZ_correct R w he hh hn s m hd0 hS0 hT0 hz0 hp0 hc0 hi0

variable (R : KRegs)

theorem diag_sq_full_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (make R) R.invF := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  have r := make_correct R w he hh hn s m hd0 (KRegs.xz hX (fun q h => List.mem_append_left _ h))
    (KRegs.xz hX (fun q h => List.mem_append_right _ h)) (KRegs.xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [KRegs.invF,r.2.2.1,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  exact ⟨rfl,rfl⟩
theorem diag_sq_cl_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (makeC R) R.invC := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  let a := m.take (measurementCount (make R))
  let b := m.drop (measurementCount (make R))
  have r := make_correct R w he hh hn s a hd0 (KRegs.xz hX (fun q h => List.mem_append_left _ h))
    (KRegs.xz hX (fun q h => List.mem_append_right _ h)) (KRegs.xz hz0 hz) hp0 hc0 hi0
  generalize hu : run (make R) a s=u at r
  have fu : ∀q,q∉R.S → q∉R.T → q∉R.dst → u.basis q=s.basis q := fun q a b c => r.2.2.2.2 q c a b
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S ∧ q∉R.T ∧ q∉R.dst) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => fu q (hl q hq).1 (hl q hq).2.1 (hl q hq).2.2)
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) : q∉R.S ∧ q∉R.T ∧ q∉R.dst :=
    let x := R.outside hn q h; ⟨x.2.1,x.2.2,x.1⟩
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := R.scl1591_correct w hn u b (by rw [r.2.2.1,lo,hi])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (KRegs.xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((fu _ (o _ (by simp)).1 (o _ (by simp)).2.1 (o _ (by simp)).2.2).trans hi0)
  have eq : run (makeC R) m s=run R.scl1591 b u := by
    rw [makeC,run_append,←hu]
  rw [eq]
  have sT := R.outside hn
  have dS : ∀q∈R.dst,q∉R.S := kdis hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have TS : ∀q∈R.T,q∉R.S := kdis hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  refine ⟨c.1.trans r.1,?_,?_,?_⟩
  · rw [kkeep c.2.2 dS,r.2.1]
  · refine ⟨c.2.1,?_⟩
    rw [kkeep c.2.2 TS,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2 q xS).trans (fu q xS xT h)

abbrev diag_sq_full_clear := Z5Diagonal.diag_sq_full_clear
abbrev diag_sq_cl_clear := Z5Diagonal.diag_sq_cl_clear

attribute [local irreducible] toffoliCount measurementCount Challenge.gateSlots

theorem make_counts_diff (w : R.W) :
    toffoliCount (make R)+11+DiagSq.parR R=toffoliCount (DiagSq.make R) ∧
    measurementCount (make R)+4+DiagSq.parR R=measurementCount (DiagSq.make R) :=
  DiagSq.makeZ_counts_rel R w

theorem make_counts (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (make R)=DiagSq.cost R-11-DiagSq.parR R ∧ measurementCount (make R)=DiagSq.cost R-4-DiagSq.parR R := by
  have a := DiagSq.makeZ_counts R w he
  unfold make
  constructor <;> omega

theorem make_support_subset (w : R.W) : wires (make R)⊆wires (DiagSq.make R) := by
  have a := R.m6w_wires; have b := R.m7g_wires; have c := R.m8g_wires
  have d := seedsT_wires R
  have e := (DiagSq.corrZ2_wires R).trans (wires_of_mem (corrZ_mem R))
  have f1 := wires_of_mem (dSubZ_mem R.lo R.dlo R.carry R.cin)
  have f2 := wires_of_mem (dSubZ_mem R.hi R.dhi R.carry R.cin)
  simp only [make,DiagSq.makeZ,DiagSq.make,headBlockZ,headBlock,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union d (Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union a b) e) f1) f2)) c

theorem makeC_support_subset (w : R.W) :
    wires (makeC R)⊆wires (FrontierSumCleanup1591Diagonal.makeC R) := by
  simp only [makeC,FrontierSumCleanup1591Diagonal.makeC,wires_append]
  exact Finset.union_subset_union (make_support_subset R w) (Finset.Subset.refl _)

theorem make_support (w : R.W) : wires (make R)⊆R.all.toFinset :=
  (make_support_subset R w).trans (DiagSq.steps_support R w).1

theorem makeC_support (w : R.W) : wires (makeC R)⊆R.all.toFinset :=
  (makeC_support_subset R w).trans (FrontierSumCleanup1591Diagonal.makeC_support R w)

theorem clear_support_subset : wires (clear R)⊆wires (FrontierSumCleanup1591Diagonal.clear R) := by
  have z8 := R.c8g_wires; have z7 := R.c7g_wires; have z6 := R.c6w_wires
  simp only [clear,Z5Diagonal.clear,FrontierSumCleanup1591Diagonal.clear,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact z8 | exact z7 | exact z6 | exact wires_of_mem (dAddZ_mem _ _ _ _) |
    exact (dAddZ2_wires_le _ _ _ _).trans (wires_of_mem (dAddZ_mem _ _ _ _)) |
    exact wires_of_mem (corrBackZ_mem R) | exact rawClearT_wires_sub _ _ _ _ | exact Finset.Subset.refl _

theorem clearC_support_subset : wires (clearC R)⊆wires (FrontierSumCleanup1591Diagonal.clearC R) := by
  simp only [clearC,Z5Diagonal.clearC,FrontierSumCleanup1591Diagonal.clearC,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (clear_support_subset R)

theorem clear_slots_old : Challenge.gateSlots (clear R)≤Challenge.gateSlots (FrontierSumCleanup1591Diagonal.clear R) := by
  have z8 := R.c8g_slots; have z7 := R.c7g_slots; have z6 := R.c6w_slots
  have rS := DiagSq.rawClearT_slots_le R.S R.T R.pad R.carry
  have rH := DiagSq.rawClearT_slots_le R.hi R.dhi R.pad R.carry
  have rL := DiagSq.rawClearT_slots_le R.lo R.dlo R.pad R.carry
  have cb := DiagSq.corrBackZ_slots R
  have da1 := DiagSq.dAddZ_slots R.lo R.dlo R.carry R.cin
  have da2 := DiagSq.dAddZ_slots R.hi R.dhi R.carry R.cin
  have db1 := DiagSq.dAddZ2_slots_eq R.lo R.dlo R.carry R.cin
  have db2 := DiagSq.dAddZ2_slots_eq R.hi R.dhi R.carry R.cin
  simp only [clear,Z5Diagonal.clear,FrontierSumCleanup1591Diagonal.clear,Challenge.gateSlots_append] at *
  omega

theorem clearC_slots_old : Challenge.gateSlots (clearC R)≤Challenge.gateSlots (FrontierSumCleanup1591Diagonal.clearC R) := by
  have h := clear_slots_old R
  simp only [clear,clearC,Z5Diagonal.clearC,FrontierSumCleanup1591Diagonal.clearC,Challenge.gateSlots_append] at *
  omega

abbrev clear_counts := Z5Diagonal.clear_counts
abbrev clear_support := Z5Diagonal.clear_support
abbrev clearC_support := Z5Diagonal.clearC_support
abbrev clear_physical := Z5Diagonal.clear_physical
abbrev clearC_physical := Z5Diagonal.clearC_physical
abbrev clear_slots_le := Z5Diagonal.clear_slots_le
abbrev clearC_slots_le := Z5Diagonal.clearC_slots_le

theorem steps_support (w : R.W) :
    wires (make R)⊆R.all.toFinset ∧ wires (clear R)⊆R.all.toFinset :=
  ⟨make_support R w,clear_support R w⟩

theorem make_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical (make R) :=
  DiagSq.makeZ_physical R w hn

theorem makeC_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeC R) :=
  (gatePhysical_append _ _).mpr ⟨make_physical R w hn,R.scl1591_physical w hn⟩

theorem steps_physical (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (make R) ∧ GatePhysical (clear R) :=
  ⟨make_physical R w hn,clear_physical R w hn⟩

theorem make_slots_le (w : R.W) :
    Challenge.gateSlots (make R)≤Challenge.gateSlots (DiagSq.make R) :=
  DiagSq.makeZ_slots R

theorem makeC_slots_old (w : R.W) :
    Challenge.gateSlots (makeC R)≤Challenge.gateSlots (FrontierSumCleanup1591Diagonal.makeC R) := by
  have z := make_slots_le R w
  simp only [makeC,FrontierSumCleanup1591Diagonal.makeC,Challenge.gateSlots_append]
  omega

theorem makeC_slots_le (w : R.W) :
    Challenge.gateSlots (makeC R)≤Challenge.gateSlots (DiagSq.makeC R) :=
  (makeC_slots_old R w).trans (FrontierSumCleanup1591Diagonal.makeC_slots_le R)

theorem tiny_slots (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (make R)≤150800 ∧ Challenge.gateSlots (clear R)≤150800 :=
  ⟨(make_slots_le R w).trans (DiagSq.tiny_slots R w he hh).1,
    (Z5Diagonal.tiny_slots R w he hh).2⟩

end ECDSAAdd.Entrant.LowZero18Diagonal

namespace ECDSAAdd.Entrant.ConstCarry
open ECDSAAdd ECDSAAdd.Arithmetic

/-- `addInPlace` whose second majority is the single CNOT `c₀ → c₁`. -/
def addInPlace2 : List Wire → List Wire → List Wire → Wire → Program
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, cin =>
      majority a0 b0 cin c0 ++ ([.CX c0 c1] ++ addInPlace (a2 :: as) (b2 :: bs) cs c1 ++
        eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++ eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0]
  | x, y, c, cin => addInPlace x y c cin

/-- `subInPlace` with `addInPlace2`. -/
def subInPlace2 (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addInPlace2 x y carry cin ++ notRegister y

theorem addInPlace_shape3 (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) :
    addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin =
      majority a0 b0 cin c0 ++ (majority a1 b1 c0 c1 ++ addInPlace (a2 :: as) (b2 :: bs) cs c1 ++
        eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++ eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0] := by
  simp only [addInPlace]

theorem run_pre (p q : Program) (hp : measurementCount p = 0) (m : List Bool) (s : State) :
    run (p ++ q) m s = run q m (run p [] s) := by
  rw [run_append, hp]; simp

theorem majority_mc (a b c d : Wire) : measurementCount (majority a b c d) = 0 := by
  simp [majority, measurementCount]

/-- When the first two inputs differ the majority is a copy of the carry-in. -/
theorem majority_ne (a b cin carry : Wire) (hnd : [a, b, cin, carry].Nodup) (s : State)
    (h : s.basis a ≠ s.basis b) :
    run (majority a b cin carry) [] s = run [.CX cin carry] [] s := by
  rw [majority_correct a b cin carry hnd]
  simp only [run]
  congr 2
  cases ha : s.basis a <;> cases hb : s.basis b <;> cases s.basis cin <;> simp_all [carryBit]

theorem notRegister_mc (r : List Wire) : measurementCount (notRegister r) = 0 := by
  induction r with
  | nil => rfl
  | cons w r ih => simpa [notRegister, measurementCount] using ih

theorem addInPlace2_run (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire)
    (h0 : [a0, b0, cin, c0].Nodup) (h1 : [a1, b1, c0, c1].Nodup) (ha : a1 ≠ c0) (hb : b1 ≠ c0)
    (s : State) (m : List Bool) (h : s.basis a1 ≠ s.basis b1) :
    run (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) m s =
      run (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) m s := by
  rw [addInPlace_shape3]
  simp only [addInPlace2, List.append_assoc]
  rw [run_pre _ _ (majority_mc _ _ _ _), run_pre _ _ (majority_mc _ _ _ _),
    run_pre [.CX c0 c1] _ (by simp [measurementCount]), run_pre _ _ (majority_mc _ _ _ _)]
  congr 1
  have t := majority_correct a0 b0 cin c0 h0 s []
  have e := majority_ne a1 b1 c0 c1 h1 (run (majority a0 b0 cin c0) [] s) (by
    rw [t]; simpa [writeBit, Function.update, ha, hb] using h)
  exact e.symm

theorem subInPlace2_run (x y carry : List Wire) (cin : Wire) (hn : (cin :: (x ++ y ++ carry)).Nodup)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) (s : State) (m : List Bool)
    (hb : s.basis (y.getD 1 0) = s.basis (x.getD 1 0)) :
    run (subInPlace2 x y carry cin) m s = run (subInPlace x y carry cin) m s := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    have hyn : (b0 :: b1 :: b2 :: bs).Nodup :=
      (List.nodup_cons.mp hn).2.sublist ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))
    simp only [List.Nodup, List.cons_append, List.pairwise_cons, List.pairwise_append, List.mem_cons,
      List.mem_append, List.append_assoc, forall_eq, or_imp, forall_and] at hn
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hb
    have mz : measurementCount (notRegister (b0 :: b1 :: b2 :: bs)) = 0 := notRegister_mc _
    have mc2 : measurementCount (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) =
        measurementCount (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) := by
      rw [addInPlace_shape3]; simp [addInPlace2, measurementCount_append, majority_mc, measurementCount]
    simp only [subInPlace2, subInPlace, List.append_assoc]
    rw [run_pre _ _ mz, run_pre _ _ mz, run_append, run_append (addInPlace _ _ _ _), mc2]
    congr 1
    rw [notRegister_correct _ hyn]
    apply addInPlace2_run
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or]; tauto
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or]; tauto
    · tauto
    · tauto
    · have a1y : a1 ∉ b0 :: b1 :: b2 :: bs := by simp only [List.mem_cons, not_or]; tauto
      have b1y : b1 ∈ b0 :: b1 :: b2 :: bs := by simp
      clear hn
      show (if a1 ∈ b0 :: b1 :: b2 :: bs then !s.basis a1 else s.basis a1) ≠
        (if b1 ∈ b0 :: b1 :: b2 :: bs then !s.basis b1 else s.basis b1)
      rw [if_neg a1y, if_pos b1y, hb]
      cases s.basis a1 <;> decide

theorem mem_addInPlace2 (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) (i : Instr)
    (h : i ∈ addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) :
    i ∈ addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin ∨ i = .CX c0 c1 := by
  rw [addInPlace_shape3]
  simp only [addInPlace2, List.mem_append, List.mem_cons, List.not_mem_nil] at h ⊢
  tauto

theorem addInPlace2_counts (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) :
    toffoliCount (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin)+1 =
      toffoliCount (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) ∧
    measurementCount (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) =
      measurementCount (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) := by
  rw [addInPlace_shape3]
  simp only [addInPlace2, toffoliCount_append, measurementCount_append]
  simp [majority, toffoliCount, measurementCount]
  omega

theorem addInPlace2_wires (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) :
    wires (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) ⊆
      wires (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) := by
  rw [addInPlace_shape3]
  simp only [addInPlace2, wires_append]
  have : wires [Instr.CX c0 c1] ⊆ wires (majority a1 b1 c0 c1) := by
    intro w hw
    simp [wires, Instr.wires, majority] at hw ⊢
    tauto
  intro w hw
  simp only [Finset.mem_union] at hw ⊢
  have := @this w
  tauto

theorem addInPlace2_slots (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) :
    Challenge.gateSlots (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) ≤
      Challenge.gateSlots (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) := by
  rw [addInPlace_shape3]
  simp only [addInPlace2, Challenge.gateSlots_append]
  simp [majority, Challenge.gateSlots, Challenge.instructionSlots]

theorem addInPlace2_physical (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire)
    (hp : GatePhysical (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin))
    (hc : c0 ≠ c1) :
    GatePhysical (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) := by
  intro i hi
  rcases mem_addInPlace2 _ _ _ _ _ _ _ _ _ _ _ _ i hi with h | h
  · exact hp i h
  · subst h; exact hc

/-- Bit 1 of a register as a function of its value. -/
theorem bit1_value (r : List Wire) (st : BasisState) (h : 2 ≤ r.length) :
    st (r.getD 1 0) = decide (regValue r st / 2 % 2 = 1) := by
  match r, h with
  | w0 :: w1 :: ws, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero, regValue, List.foldr_cons]
    by_cases h0 : st w0 <;> by_cases h1 : st w1 <;> simp [h0, h1] <;> omega

/-- Bit 1 of a square is clear. -/
theorem sq_bit1 (n : Nat) : n^2 / 2 % 2 = 0 := by
  have h : n^2 % 4 = (n % 4)^2 % 4 := Nat.pow_mod n 2 4
  have : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have e : n^2 / 2 % 2 = n^2 % 4 / 2 := by omega
  rw [e, h]
  interval_cases (n % 4) <;> norm_num

theorem subInPlace2_counts (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    toffoliCount (subInPlace2 x y carry cin)+1=toffoliCount (subInPlace x y carry cin) ∧
    measurementCount (subInPlace2 x y carry cin)=measurementCount (subInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    have e := addInPlace2_counts a0 a1 a2 b0 b1 b2 c0 c1 cin as bs cs
    simp only [subInPlace2, subInPlace, toffoliCount_append, measurementCount_append]
    omega

theorem subInPlace2_wires (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    wires (subInPlace2 x y carry cin)⊆wires (subInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    have e := addInPlace2_wires a0 a1 a2 b0 b1 b2 c0 c1 cin as bs cs
    simp only [subInPlace2, subInPlace, wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) e) (Finset.Subset.refl _)

theorem subInPlace2_slots (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    Challenge.gateSlots (subInPlace2 x y carry cin)≤Challenge.gateSlots (subInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    have e := addInPlace2_slots a0 a1 a2 b0 b1 b2 c0 c1 cin as bs cs
    simp only [subInPlace2, subInPlace, Challenge.gateSlots_append]
    omega

theorem subInPlace2_physical (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) (hnd : carry.Nodup)
    (hp : GatePhysical (subInPlace x y carry cin)) : GatePhysical (subInPlace2 x y carry cin) := by
  match x, y, carry, hx, hy, hc, hnd with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _, hnd =>
    simp only [subInPlace2, subInPlace, gatePhysical_append] at hp ⊢
    refine ⟨⟨hp.1.1, addInPlace2_physical _ _ _ _ _ _ _ _ _ _ _ _ hp.1.2 ?_⟩, hp.2⟩
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    exact hnd.1.1

end ECDSAAdd.Entrant.ConstCarry

namespace ECDSAAdd.Entrant.KRegs
open ECDSAAdd ECDSAAdd.Arithmetic
variable (R : KRegs)

/-- `m6` with the second majority of its carry chain reduced to one CNOT. -/
def m6c : Program := ConstCarry.subInPlace2 (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem m6c_lens (w : R.W) : 3 ≤ (R.dlo++R.zA).length ∧ 3 ≤ R.T.length ∧ 2 ≤ (R.carry.take (R.T.length-1)).length ∧
    2 ≤ R.dlo.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  simp only [List.length_append, List.length_take]
  omega

theorem m6c_counts (w : R.W) : toffoliCount R.m6c+1=toffoliCount R.m6 ∧
    measurementCount R.m6c=measurementCount R.m6 := by
  have l := R.m6c_lens w
  exact ConstCarry.subInPlace2_counts _ _ _ _ l.1 l.2.1 l.2.2.1

theorem m6c_wires (w : R.W) : wires R.m6c⊆wires R.m6 := by
  have l := R.m6c_lens w
  exact ConstCarry.subInPlace2_wires _ _ _ _ l.1 l.2.1 l.2.2.1

theorem m6c_slots (w : R.W) : Challenge.gateSlots R.m6c≤Challenge.gateSlots R.m6 := by
  have l := R.m6c_lens w
  exact ConstCarry.subInPlace2_slots _ _ _ _ l.1 l.2.1 l.2.2.1

theorem m6c_physical (w : R.W) (hc : (R.carry.take (R.T.length-1)).Nodup) (hp : GatePhysical R.m6) :
    GatePhysical R.m6c := by
  have l := R.m6c_lens w
  exact ConstCarry.subInPlace2_physical _ _ _ _ l.1 l.2.1 l.2.2.1 hc hp

theorem carry_take_nodup (hn : R.all.Nodup) (n : Nat) : (R.carry.take n).Nodup :=
  hn.sublist ((List.take_sublist _ _).trans ((List.sublist_append_right _ _).trans (List.sublist_cons_self _ _)))

/-- With bit 1 of `T` equal to bit 1 of the diagonal, `m6c` runs exactly like `m6`. -/
theorem m6c_run (w : R.W) (hn : (R.cin::((R.dlo++R.zA)++R.T++R.carry.take (R.T.length-1))).Nodup)
    (s : State) (m : List Bool) (hb : s.basis (R.T.getD 1 0)=s.basis (R.dlo.getD 1 0)) :
    run R.m6c m s=run R.m6 m s := by
  have l := R.m6c_lens w
  apply ConstCarry.subInPlace2_run _ _ _ _ hn l.1 l.2.1 l.2.2.1
  rw [hb, List.getD_append _ _ _ _ (by omega)]

/-- Squares: bit 1 of `T` and of the low diagonal are both clear. -/
theorem m6c_bits (w : R.W) (st : BasisState) (A B : Nat) (hT : regValue R.T st=A^2)
    (hd : regValue R.dlo st=B^2) : st (R.T.getD 1 0)=st (R.dlo.getD 1 0) := by
  have l := R.m6c_lens w
  rw [ConstCarry.bit1_value R.T st (by omega), ConstCarry.bit1_value R.dlo st l.2.2.2, hT, hd,
    ConstCarry.sq_bit1, ConstCarry.sq_bit1]

end ECDSAAdd.Entrant.KRegs

namespace ECDSAAdd.Entrant.ConstCarry
open ECDSAAdd ECDSAAdd.Arithmetic

/-- `addInPlace` whose second majority is the single CNOT `b₁ → c₁`. -/
def addInPlace3 : List Wire → List Wire → List Wire → Wire → Program
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, cin =>
      majority a0 b0 cin c0 ++ ([.CX b1 c1] ++ addInPlace (a2 :: as) (b2 :: bs) cs c1 ++
        eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++ eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0]
  | x, y, c, cin => addInPlace x y c cin

/-- When the second and third inputs agree the majority is a copy of the second. -/
theorem majority_eq (a b cin carry : Wire) (hnd : [a, b, cin, carry].Nodup) (s : State)
    (h : s.basis b = s.basis cin) :
    run (majority a b cin carry) [] s = run [.CX b carry] [] s := by
  rw [majority_correct a b cin carry hnd]
  simp only [run]
  congr 2
  rw [← h]
  cases s.basis a <;> cases s.basis b <;> simp [carryBit]

theorem addInPlace3_run (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire)
    (h0 : [a0, b0, cin, c0].Nodup) (h1 : [a1, b1, c0, c1].Nodup) (hb : b1 ≠ c0)
    (s : State) (m : List Bool) (hc : s.basis c0 = false)
    (h : s.basis b1 = carryBit (s.basis a0) (s.basis b0) (s.basis cin)) :
    run (addInPlace3 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) m s =
      run (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) m s := by
  rw [addInPlace_shape3]
  simp only [addInPlace3, List.append_assoc]
  rw [run_pre _ _ (majority_mc _ _ _ _), run_pre _ _ (majority_mc _ _ _ _),
    run_pre [.CX b1 c1] _ (by simp [measurementCount]), run_pre _ _ (majority_mc _ _ _ _)]
  congr 1
  have t := majority_correct a0 b0 cin c0 h0 s []
  have e := majority_eq a1 b1 c0 c1 h1 (run (majority a0 b0 cin c0) [] s) (by
    rw [t]; simp [writeBit, Function.update, hb, hc, h])
  exact e.symm

theorem mem_addInPlace3 (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) (i : Instr)
    (h : i ∈ addInPlace3 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) :
    i ∈ addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin ∨ i = .CX b1 c1 := by
  rw [addInPlace_shape3]
  simp only [addInPlace3, List.mem_append, List.mem_cons, List.not_mem_nil] at h ⊢
  tauto

/-- Same run as `addInPlace` when bit 1 of `y` equals the bit-0 carry, with clean carries. -/
theorem addInPlace3_run_list (x y carry : List Wire) (cin : Wire) (hn : (cin :: (x ++ y ++ carry)).Nodup)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) (s : State) (m : List Bool)
    (hc0 : s.basis (carry.getD 0 0) = false)
    (hb : s.basis (y.getD 1 0) = carryBit (s.basis (x.getD 0 0)) (s.basis (y.getD 0 0)) (s.basis cin)) :
    run (addInPlace3 x y carry cin) m s = run (addInPlace x y carry cin) m s := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    simp only [List.Nodup, List.cons_append, List.pairwise_cons, List.pairwise_append, List.mem_cons,
      List.mem_append, List.append_assoc, forall_eq, or_imp, forall_and] at hn
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hb hc0
    apply addInPlace3_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc0 hb
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or]; tauto
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or]; tauto
    · tauto

theorem addInPlace3_counts (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    toffoliCount (addInPlace3 x y carry cin)+1=toffoliCount (addInPlace x y carry cin) ∧
    measurementCount (addInPlace3 x y carry cin)=measurementCount (addInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    rw [addInPlace_shape3]
    simp only [addInPlace3, toffoliCount_append, measurementCount_append]
    simp [majority, toffoliCount, measurementCount]
    omega

theorem addInPlace3_wires (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    wires (addInPlace3 x y carry cin)⊆wires (addInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    rw [addInPlace_shape3]
    simp only [addInPlace3, wires_append]
    have : wires [Instr.CX b1 c1] ⊆ wires (majority a1 b1 c0 c1) := by
      intro w hw
      simp [wires, Instr.wires, majority] at hw ⊢
      tauto
    intro w hw
    simp only [Finset.mem_union] at hw ⊢
    have := @this w
    tauto

theorem addInPlace3_slots (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    Challenge.gateSlots (addInPlace3 x y carry cin)≤Challenge.gateSlots (addInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    rw [addInPlace_shape3]
    simp only [addInPlace3, Challenge.gateSlots_append]
    simp [majority, Challenge.gateSlots, Challenge.instructionSlots]

theorem addInPlace3_physical (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length)
    (hp : GatePhysical (addInPlace x y carry cin)) : GatePhysical (addInPlace3 x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    have hm : Instr.CCX b1 c0 c1 ∈ addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin := by
      rw [addInPlace_shape3]; simp [majority]
    have pc := hp _ hm
    intro i hi
    rcases mem_addInPlace3 _ _ _ _ _ _ _ _ _ _ _ _ i hi with h | h
    · exact hp i h
    · subst h; exact pc.1

/-- Bit 0 of a register as a function of its value. -/
theorem bit0_value (r : List Wire) (st : BasisState) (h : 1 ≤ r.length) :
    st (r.getD 0 0) = decide (regValue r st % 2 = 1) := by
  match r, h with
  | w0 :: ws, _ =>
    simp only [List.getD_cons_zero, regValue, List.foldr_cons]
    by_cases h0 : st w0 <;> simp [h0]

theorem getD0_mem (l : List Wire) (h : 1 ≤ l.length) : l.getD 0 0 ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs => simp

theorem cross_bits (A B : Nat) :
    (2*A*B+B^2) / 2 % 2 = 1 ↔ (A^2 % 2 = 1 ∧ (2*A*B+B^2) % 2 = 1) := by
  have h1 : (2*A*B+B^2) % 4 = (2*(A%4)*(B%4)+(B%4)^2) % 4 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have h2 : A^2 % 2 = (A%4)^2 % 2 := by
    rw [Nat.pow_mod]; conv_rhs => rw [Nat.pow_mod]
    congr 2; omega
  have e1 : (2*A*B+B^2) / 2 % 2 = (2*A*B+B^2) % 4 / 2 := by omega
  have e2 : (2*A*B+B^2) % 2 = (2*A*B+B^2) % 4 % 2 := by omega
  rw [e1, e2, h1, h2]
  have : A % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have : B % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (A % 4) <;> interval_cases (B % 4) <;> norm_num

end ECDSAAdd.Entrant.ConstCarry

namespace ECDSAAdd.Entrant.KRegs
open ECDSAAdd ECDSAAdd.Arithmetic
variable (R : KRegs)

/-- `c6` with the second majority of its carry chain reduced to one CNOT. -/
def c6c : Program := ConstCarry.addInPlace3 (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem c6c_counts (w : R.W) : toffoliCount R.c6c+1=toffoliCount R.c6 ∧
    measurementCount R.c6c=measurementCount R.c6 := by
  have l := R.m6c_lens w
  exact ConstCarry.addInPlace3_counts _ _ _ _ l.1 l.2.1 l.2.2.1

theorem c6c_wires (w : R.W) : wires R.c6c⊆wires R.c6 := by
  have l := R.m6c_lens w
  exact ConstCarry.addInPlace3_wires _ _ _ _ l.1 l.2.1 l.2.2.1

theorem c6c_slots (w : R.W) : Challenge.gateSlots R.c6c≤Challenge.gateSlots R.c6 := by
  have l := R.m6c_lens w
  exact ConstCarry.addInPlace3_slots _ _ _ _ l.1 l.2.1 l.2.2.1

theorem c6c_physical (w : R.W) (hp : GatePhysical R.c6) : GatePhysical R.c6c := by
  have l := R.m6c_lens w
  exact ConstCarry.addInPlace3_physical _ _ _ _ l.1 l.2.1 l.2.2.1 hp

/-- With bit 1 of `T` equal to the bit-0 carry of `dlo + T`, `c6c` runs exactly like `c6`. -/
theorem c6c_run (w : R.W) (hn : (R.cin::((R.dlo++R.zA)++R.T++R.carry.take (R.T.length-1))).Nodup)
    (s : State) (m : List Bool) (hc0 : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hi : s.basis R.cin=false)
    (hb : s.basis (R.T.getD 1 0)=(s.basis (R.dlo.getD 0 0) && s.basis (R.T.getD 0 0))) :
    run R.c6c m s=run R.c6 m s := by
  have l := R.m6c_lens w
  apply ConstCarry.addInPlace3_run_list _ _ _ _ hn l.1 l.2.1 l.2.2.1
  · exact hc0 _ (ConstCarry.getD0_mem _ (by omega))
  · rw [hb, List.getD_append _ _ _ _ (by omega), hi]
    cases s.basis (R.dlo.getD 0 0) <;> cases s.basis (R.T.getD 0 0) <;> rfl

theorem c6c_bits (w : R.W) (st : BasisState) (A B : Nat) (hT : regValue R.T st=2*A*B+B^2)
    (hd : regValue R.dlo st=A^2) : st (R.T.getD 1 0)=(st (R.dlo.getD 0 0) && st (R.T.getD 0 0)) := by
  have l := R.m6c_lens w
  rw [ConstCarry.bit1_value R.T st (by omega), ConstCarry.bit0_value R.T st (by omega),
    ConstCarry.bit0_value R.dlo st (by omega), hT, hd]
  have := ConstCarry.cross_bits A B
  by_cases h1 : A^2 % 2 = 1 <;> by_cases h2 : (2*A*B+B^2) % 2 = 1 <;> simp_all

end ECDSAAdd.Entrant.KRegs

section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Entrant.KRegs
open ECDSAAdd ECDSAAdd.Arithmetic

/-! In the 129-bit leaf (`2h+1 ≤ n`), `T = 2ab+b² < 2^(|T|-1)` before `T −= b²` and after
`T += b²`, so the borrow/carry into the top bit of `T` is always zero and both adders can run
on the low `|T|-1` bits (one majority/erase pair fewer each). -/

theorem addHeadI_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+3)
    (hy : y.length=n+3) (hc : c.length=n+2) :
    (addHeadI (x.take (n+2)) (y.take (n+2)) (c.take (n+1)) cin).Sublist (addHeadI x y c cin) := by
  match x, y, c, hx, hy, hc with
  | a::a'::x', b::b'::y', c0::c', hx, hy, hc =>
    have r := add_take_sublist n (a'::x') (b'::y') c' c0 (by simpa using hx) (by simpa using hy)
      (by simpa using hc)
    simp only [List.take_succ_cons] at r ⊢
    simp only [addHeadI]
    exact (List.Sublist.refl _).append ((r.append (List.Sublist.refl _)).append (List.Sublist.refl _))

theorem addLowNC1_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+4)
    (hy : y.length=n+4) (hc : c.length=n+3) :
    (addLowNC1 (x.take (n+3)) (y.take (n+3)) (c.take (n+2)) cin).Sublist (addLowNC1 x y c cin) := by
  match x, y, c, hx, hy, hc with
  | a::x', b::y', c0::c', hx, hy, hc =>
    have r := addHeadI_take_sublist n x' y' c' cin (by simpa using hx) (by simpa using hy)
      (by simpa using hc)
    simp only [addLowNC1,List.take_succ_cons,List.tail_cons,List.headD_cons]
    exact (r.append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem subLowNC1_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+4)
    (hy : y.length=n+4) (hc : c.length=n+3) :
    (subLowNC1 (x.take (n+3)) (y.take (n+3)) (c.take (n+2)) cin).Sublist (subLowNC1 x y c cin) := by
  simp only [subLowNC1]
  exact ((notRegister_take_sublist y (n+3)).append (addLowNC1_take_sublist n x y c cin hx hy hc)).append
    (notRegister_take_sublist y (n+3))

theorem take_tail_headD (l : List Wire) (k : Nat) (hk : 2≤k) : (l.take k).tail.headD 0=l.tail.headD 0 := by
  rcases l with _|⟨a,l⟩
  · simp
  · obtain ⟨j,rfl⟩ : ∃j,k=j+1 := ⟨k-1,by omega⟩
    simp only [List.take_succ_cons,List.tail_cons]
    exact take_headD l j (by omega)

theorem trim_pow (n h : Nat) : 2^(2*(n-h+1)-1)=2*2^(n-h)*2^(n-h) := by
  rw [show 2*(n-h+1)-1=((n-h)+(n-h))+1 by omega,pow_succ,pow_add]; ring

theorem trim_bound (n h a b : Nat) (hc : 2*h+1≤n) (ha : a<2^h) (hb : b<2^(n-h)) :
    2*a*b+b^2<2^(2*(n-h+1)-1) := by
  rw [trim_pow]
  have hB : 2*2^h≤2^(n-h) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2^(n-h)=B at *
  have h2a : 2*a+1≤B := by omega
  have h1 := Nat.mul_le_mul_right b h2a
  have h2 : b*b≤b*B := Nat.mul_le_mul_left b hb.le
  have h3 : b*B<B*B := Nat.mul_lt_mul_of_pos_right hb (by omega)
  nlinarith

theorem sq_trim_bound (n h b : Nat) (hb : b<2^(n-h)) : b^2<2^(2*(n-h+1)-1) := by
  rw [trim_pow]
  generalize 2^(n-h)=B at *
  have h2 : b*b≤b*B := Nat.mul_le_mul_left b hb.le
  have h3 : b*B<B*B := Nat.mul_lt_mul_of_pos_right hb (by omega)
  nlinarith

variable (R : KRegs)

def trimOK : Prop := 2*R.h+1≤R.bank.length
instance : Decidable R.trimOK := by unfold trimOK; infer_instance

def topOK : Prop := R.trimOK ∧ (R.dhi++R.zB).length=R.T.length ∧
  (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 4≤R.T.length
instance : Decidable R.topOK := by unfold topOK; infer_instance

/-- `m7y` on the low `|T|-1` bits when the top bit of `T` is provably clear. -/
def m7t : Program := if R.topOK then
  subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.m7y
/-- `c7y` on the low `|T|-1` bits when the top bit of `T` is provably clear. -/
def c7t : Program := if R.topOK then
  addLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.c7y

theorem topOK_of (w : R.W) (hc : R.trimOK) : R.topOK := by
  have l := R.t_lensg w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have hSl := w.S; have hTl := w.T
  exact ⟨hc,l.1,l.2.1,by omega⟩

theorem m7t_sub : R.m7t.Sublist R.m7y := by
  unfold m7t
  split_ifs with h
  · obtain ⟨-,h1,h2,h3⟩ := h
    have e : R.m7y=subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin :=
      if_pos ⟨h1,h2,by omega⟩
    rw [e]
    have e1 : R.T.length-1=(R.T.length-4)+3 := by omega
    have e2 : R.T.length-2=(R.T.length-4)+2 := by omega
    rw [e1,e2]
    exact subLowNC1_take_sublist _ _ _ _ _ (by omega) (by omega)
      (by rw [List.length_take]; simp only [List.length_take] at h2; omega)
  · exact List.Sublist.refl _

theorem c7t_sub : R.c7t.Sublist R.c7y := by
  unfold c7t
  split_ifs with h
  · obtain ⟨-,h1,h2,h3⟩ := h
    have e : R.c7y=addLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin :=
      if_pos ⟨h1,h2,by omega⟩
    rw [e]
    have e1 : R.T.length-1=(R.T.length-4)+3 := by omega
    have e2 : R.T.length-2=(R.T.length-4)+2 := by omega
    rw [e1,e2]
    exact addLowNC1_take_sublist _ _ _ _ _ (by omega) (by omega)
      (by rw [List.length_take]; simp only [List.length_take] at h2; omega)
  · exact List.Sublist.refl _

theorem m7t_wires : wires R.m7t⊆wires R.m7 :=
  (DiagSq.wires_of_mem (fun _ h => (R.m7t_sub).subset h)).trans R.m7y_wires
theorem c7t_wires : wires R.c7t⊆wires R.c7 :=
  (DiagSq.wires_of_mem (fun _ h => (R.c7t_sub).subset h)).trans R.c7y_wires
theorem m7t_physical (hn : R.all.Nodup) : GatePhysical R.m7t :=
  fun i h => R.m7y_physical hn i ((R.m7t_sub).subset h)
theorem c7t_physical (hn : R.all.Nodup) : GatePhysical R.c7t :=
  fun i h => R.c7y_physical hn i ((R.c7t_sub).subset h)
theorem m7t_slots : Challenge.gateSlots R.m7t≤Challenge.gateSlots R.m7 :=
  (slots_sublist R.m7t_sub).trans R.m7y_slots
theorem c7t_slots : Challenge.gateSlots R.c7t≤Challenge.gateSlots R.c7 :=
  (slots_sublist R.c7t_sub).trans R.c7y_slots

theorem m7t_counts (w : R.W) : toffoliCount R.m7t+(if R.trimOK then 1 else 0)+2=toffoliCount R.m7 ∧
    measurementCount R.m7t+(if R.trimOK then 1 else 0)=measurementCount R.m7 := by
  have y := R.m7y_counts w
  have l := R.t_lensg w
  by_cases hc : R.trimOK
  · rw [if_pos hc]
    obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
    have h4 := w.h4; have hh := w.hh; have hSl := w.S; have hTl := w.T
    have em : R.m7t=subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos (R.topOK_of w hc)
    have ey : R.m7y=subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin :=
      if_pos ⟨l.1,l.2.1,l.2.2.1⟩
    have lx : ((R.dhi++R.zB).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
      simp only [List.length_take]; omega
    have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
      have := l.2.1; simp only [List.length_take] at this ⊢; omega
    have a := subLowNC1_counts ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin
      (by rw [lx]; simp only [List.length_take]; omega) (by simp only [List.length_take]; omega)
      (by simp only [List.length_take] at lc ⊢; omega)
    have b := LowZero.subLowNC_counts _ _ _ R.cin lx lc (by simp only [List.length_take]; omega)
    have c := subInPlace_counts _ _ _ R.cin lx lc
    have a' := subLowNC1_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
      (by rw [l.1]; omega) (by omega) (by have := l.2.1; omega)
    have b' := LowZero.subLowNC_counts _ _ _ R.cin l.1 l.2.1 l.2.2.1
    have c' := subInPlace_counts _ _ _ R.cin l.1 l.2.1
    have ma : measurementCount (subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin)=
        measurementCount (LowZero.subLowNC ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) := by
      simp only [subLowNC1,LowZero.subLowNC,measurementCount_append,addLowNC1_mc]
    have ma' : measurementCount (subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin)=
        measurementCount (LowZero.subLowNC (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin) := by
      simp only [subLowNC1,LowZero.subLowNC,measurementCount_append,addLowNC1_mc]
    rw [em]; rw [ey] at y
    simp only [List.length_take] at c
    constructor <;> omega
  · rw [if_neg hc]
    have em : R.m7t=R.m7y := if_neg (fun h => hc h.1)
    rw [em]; exact ⟨by omega,by omega⟩

theorem c7t_counts (w : R.W) : toffoliCount R.c7t+(if R.trimOK then 1 else 0)+2=toffoliCount R.c7 ∧
    measurementCount R.c7t+(if R.trimOK then 1 else 0)=measurementCount R.c7 := by
  have y := R.c7y_counts w
  have l := R.t_lensg w
  by_cases hc : R.trimOK
  · rw [if_pos hc]
    obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
    have h4 := w.h4; have hh := w.hh; have hSl := w.S; have hTl := w.T
    have em : R.c7t=addLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos (R.topOK_of w hc)
    have ey : R.c7y=addLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin :=
      if_pos ⟨l.1,l.2.1,l.2.2.1⟩
    have lx : ((R.dhi++R.zB).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
      simp only [List.length_take]; omega
    have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
      have := l.2.1; simp only [List.length_take] at this ⊢; omega
    have a := addLowNC1_counts ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin
      (by rw [lx]; simp only [List.length_take]; omega) (by simp only [List.length_take]; omega)
      (by simp only [List.length_take] at lc ⊢; omega)
    have b := LowZero.addLowNC_counts _ _ _ R.cin lx lc (by simp only [List.length_take]; omega)
    have c := addInPlace_counts _ _ _ R.cin lx lc
    have a' := addLowNC1_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
      (by rw [l.1]; omega) (by omega) (by have := l.2.1; omega)
    have b' := LowZero.addLowNC_counts _ _ _ R.cin l.1 l.2.1 l.2.2.1
    have c' := addInPlace_counts _ _ _ R.cin l.1 l.2.1
    have ma := addLowNC1_mc ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin
    have ma' := addLowNC1_mc (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    rw [em]; rw [ey] at y
    simp only [List.length_take] at c
    constructor <;> omega
  · rw [if_neg hc]
    have em : R.c7t=R.c7y := if_neg (fun h => hc h.1)
    rw [em]; exact ⟨by omega,by omega⟩

theorem top_nodup (hn : R.all.Nodup) :
    (R.cin::(((R.dhi++R.zB).take (R.T.length-1))++(R.T.take (R.T.length-1))++
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)))).Nodup := by
  have full : (R.cin::((R.dhi++R.zB)++R.T++(R.carry.take (R.T.length-1)))).Nodup :=
    knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  exact full.sublist ((((List.take_sublist _ _).append (List.take_sublist _ _)).append
    (List.take_sublist _ _)).cons₂ _)

theorem m7t_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false)
    (hA : R.trimOK → regValue (R.dhi++R.zB) s.basis<2^(R.T.length-1))
    (hb : R.trimOK → regValue (R.dhi++R.zB) s.basis≤regValue R.T s.basis%2^(R.T.length-1)) :
    (run R.m7t m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7t m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7t m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  by_cases hc : R.trimOK
  swap
  · have em : R.m7t=R.m7y := if_neg (fun h => hc h.1)
    rw [em]; exact R.m7y_correct w hn s m hcl hnc hi h1
  have hA := hA hc
  have hb := hb hc
  have top := R.topOK_of w hc
  obtain ⟨-,h1l,h2,h3⟩ := top
  have em : R.m7t=subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos (R.topOK_of w hc)
  have lx : ((R.dhi++R.zB).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have hTn : R.T.Nodup := knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have e2 := subLowNC1_run ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin m s (R.top_nodup hn) hi
      (by rw [take_tail_headD _ _ (by omega)]; exact h1) (by simp only [List.length_take]; omega)
  have r := LowZero.subLowNC_correct _ _ _ R.cin (R.top_nodup hn) lx lc (by simp only [List.length_take]; omega) s m
    (fun q h => hcl q (List.mem_of_mem_take h))
    (by rw [take_headD _ _ (by omega),take_headD _ _ (by omega)]; exact hnc) hi
  rw [em,e2]
  refine ⟨r.1,fun q h => r.2.1 q (fun h' => h (List.mem_of_mem_take h')),?_⟩
  set t := run (LowZero.subLowNC ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) m s with ht
  set P := 2^(R.T.length-1) with hP
  have h2P : 2^R.T.length=2*P := by rw [hP,← pow_succ']; congr 1; omega
  have xv : regValue ((R.dhi++R.zB).take (R.T.length-1)) s.basis=regValue (R.dhi++R.zB) s.basis := by
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
  have lowv : regValue (R.T.take (R.T.length-1)) t.basis=regValue R.T s.basis%P-regValue (R.dhi++R.zB) s.basis := by
    rw [r.2.2,xv,yv,hi,Bool.toNat_false,Nat.sub_zero,List.length_take,Nat.min_eq_left (by omega),← hP]
    rw [show regValue R.T s.basis%P+P-regValue (R.dhi++R.zB) s.basis=
      (regValue R.T s.basis%P-regValue (R.dhi++R.zB) s.basis)+P by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (by have := Nat.mod_lt (regValue R.T s.basis) Ppos; omega)]
  rw [split t.basis,lowv,dkeep,dv,hi,Bool.toNat_false,Nat.sub_zero,h2P]
  have mle := Nat.mod_le (regValue R.T s.basis) P
  generalize regValue R.T s.basis%P=M at *
  generalize regValue R.T s.basis/P=D at *
  generalize regValue R.T s.basis=TV at *
  generalize regValue (R.dhi++R.zB) s.basis=AV at *
  have dq : P*D=TV-M := by omega
  rw [dq,show TV+2*P-AV=(TV-AV)+2*P by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  omega

theorem c7t_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false)
    (hA : R.trimOK → regValue (R.dhi++R.zB) s.basis<2^(R.T.length-1))
    (hb : R.trimOK → regValue R.T s.basis%2^(R.T.length-1)+regValue (R.dhi++R.zB) s.basis<2^(R.T.length-1)) :
    (run R.c7t m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7t m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7t m s).basis=(regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  by_cases hc : R.trimOK
  swap
  · have em : R.c7t=R.c7y := if_neg (fun h => hc h.1)
    rw [em]; exact R.c7y_correct w hn s m hcl hnc hi h1
  have hA := hA hc
  have hb := hb hc
  have top := R.topOK_of w hc
  obtain ⟨-,h1l,h2,h3⟩ := top
  have em : R.c7t=addLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos (R.topOK_of w hc)
  have lx : ((R.dhi++R.zB).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have hTn : R.T.Nodup := knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have e2 := addLowNC1_run ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin m s (R.top_nodup hn) hi
      (by rw [take_tail_headD _ _ (by omega)]; exact h1)
  have r := LowZero.addLowNC_correct _ _ _ R.cin (R.top_nodup hn) lx lc (by simp only [List.length_take]; omega) s m
    (fun q h => hcl q (List.mem_of_mem_take h))
    (by rw [take_headD _ _ (by omega),take_headD _ _ (by omega)]; exact hnc) hi
  rw [em,e2]
  refine ⟨r.1,fun q h => r.2.1 q (fun h' => h (List.mem_of_mem_take h')),?_⟩
  set t := run (LowZero.addLowNC ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) m s with ht
  set P := 2^(R.T.length-1) with hP
  have h2P : 2^R.T.length=2*P := by rw [hP,← pow_succ']; congr 1; omega
  have xv : regValue ((R.dhi++R.zB).take (R.T.length-1)) s.basis=regValue (R.dhi++R.zB) s.basis := by
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
  have lowv : regValue (R.T.take (R.T.length-1)) t.basis=regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis%P := by
    rw [r.2.2,xv,yv,hi,Bool.toNat_false,Nat.add_zero,List.length_take,Nat.min_eq_left (by omega),← hP]
    exact Nat.mod_eq_of_lt (by omega)
  rw [split t.basis,lowv,dkeep,dv,hi,Bool.toNat_false,Nat.add_zero,h2P]
  have mle := Nat.mod_le (regValue R.T s.basis) P
  have dle : regValue R.T s.basis/P≤1 := by
    have := Nat.div_lt_of_lt_mul (show regValue R.T s.basis<P*2 by omega); omega
  generalize regValue R.T s.basis%P=M at *
  generalize regValue R.T s.basis/P=D at *
  generalize regValue R.T s.basis=TV at *
  generalize regValue (R.dhi++R.zB) s.basis=AV at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp dle with e|e
  · subst e; simp only [Nat.mul_zero,Nat.add_zero] at md ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · subst e; simp only [Nat.mul_one] at md ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega

end ECDSAAdd.Entrant.KRegs

section
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.KnownTop
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant.TopCarry

/-- In-place adder whose highest carry is the affine bit `a' ⊕ b' ⊕ r`; valid when bit
`n-1` of the sum is known to be `r`. -/
def addKT (r : Bool) : List Wire → List Wire → List Wire → Wire → Program
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, cin =>
      (if as = [] then ([.CX a' c, .CX b' c] ++ (if r then [.X c] else [])) else majority a b cin c) ++
        addKT r (a' :: as) (b' :: bs) cs c ++ eraseCarry a b cin c ++ [.CX a b, .CX cin b]
  | [a], [b], _, cin => [.CX a b, .CX cin b]
  | _, _, _, _ => []

theorem addKT_counts (r : Bool) : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    toffoliCount (addKT r x y carry cin) = n ∧
    measurementCount (addKT r x y carry cin) = n + 1 := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    cases r <;> simp [addKT, eraseCarry, toffoliCount, measurementCount]
  | succ n ih =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have h := ih (a' :: a'' :: as) (b' :: b'' :: bs) cs c (by simpa using hy)
        (by simpa using hx) (by simpa using hc)
    simp only [addKT, List.cons_ne_nil, if_false, toffoliCount_append,
        measurementCount_append, h.1, h.2, majority, eraseCarry, toffoliCount, measurementCount]
    omega

private theorem kt_base (A A' B B' C r : Bool)
    (hS : (2 ≤ (A.toNat + 2 * A'.toNat + (B.toNat + 2 * B'.toNat) + C.toNat) % 4) = (r = true)) :
    carryBit A B C = (A' ^^ B' ^^ r) := by
  revert hS
  cases A <;> cases A' <;> cases B <;> cases B' <;> cases C <;> cases r <;> decide

/-- The affine top carry agrees with the majority whenever the top sum bit is `r`. -/
theorem addKT_eq (r : Bool) : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    (cin :: (x ++ y ++ carry)).Nodup → ∀ (s : State) (m : List Bool),
    (∀ w ∈ carry, s.basis w = false) →
    (2^(n+1) ≤ (regValue x s.basis + regValue y s.basis + (s.basis cin).toNat) % 2^(n+2)) = (r = true) →
    run (addKT r x y carry cin) m s = run (addInPlace x y carry cin) m s := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc hnd s m hclean hS
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have ha'c : a' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hb'c : b' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hzero : s.basis c = false := hclean c (by simp)
    have hK : carryBit (s.basis a) (s.basis b) (s.basis cin) = (s.basis a' ^^ s.basis b' ^^ r) := by
      apply kt_base
      simpa [regValue_cons', regValue_nil'] using hS
    have hm1 : measurementCount (([.CX a' c, .CX b' c] ++ (if r then [.X c] else [])) : Program) = 0 := by
      cases r <;> rfl
    have hm2 : measurementCount (majority a b cin c) = 0 := rfl
    have hmid : run (([.CX a' c, .CX b' c] ++ (if r then [.X c] else [])) : Program) [] s =
        run (majority a b cin c) [] s := by
      rw [majority_correct _ _ _ _ h4]
      cases r <;>
      · simp only [run, List.cons_append, List.nil_append, if_true, if_false, Bool.false_eq_true]
        apply State.extensionality
        · rfl
        · funext w
          simp only [writeBit, Function.update]
          by_cases hwc : w = c
          · subst hwc
            simp [ha'c, hb'c, hzero, hK]
          · simp [hwc]
    simp only [addKT, addInPlace, if_pos (rfl : ([] : List Wire) = []), List.append_assoc]
    exact run_head_congr _ _ _ m s hm1 hm2 hmid
  | succ n ih =>
    intro x y carry cin hy hx hc hnd s m hclean hS
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have hnd' : (c :: ((a' :: a'' :: as) ++ (b' :: b'' :: bs) ++ cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append] at this ⊢; omega
    have hcx : c ∉ a' :: a'' :: as := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hcy : c ∉ b' :: b'' :: bs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hccs : c ∉ cs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hzero : s.basis c = false := hclean c (by simp)
    let A := s.basis a
    let B := s.basis b
    let C := s.basis cin
    let s1 : State := ⟨s.phase, writeBit s.basis c (carryBit A B C)⟩
    have hfirst (record : List Bool) : run (majority a b cin c) record s = s1 := by
      rw [majority_correct _ _ _ _ h4]; simp [s1, hzero, A, B, C]
    have hs1 (w : Wire) (hw : w ≠ c) : s1.basis w = s.basis w := by simp [s1, writeBit, hw]
    have hclean' : ∀ d ∈ cs, s1.basis d = false := by
      intro d hd; rw [hs1 d (fun h => hccs (h ▸ hd))]; exact hclean d (by simp [hd])
    have hxs : regValue (a' :: a'' :: as) s1.basis = regValue (a' :: a'' :: as) s.basis :=
      regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcx (h ▸ hw)))
    have hys : regValue (b' :: b'' :: bs) s1.basis = regValue (b' :: b'' :: bs) s.basis :=
      regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcy (h ▸ hw)))
    have hc1 : s1.basis c = carryBit A B C := by simp [s1, writeBit]
    have hp3 : 2^(n+1+2) = 2 * 2^(n+2) := by rw [show n+1+2 = (n+2)+1 by omega, pow_succ]; ring
    have hp2 : 2^(n+1+1) = 2 * 2^(n+1) := by rw [pow_succ]; ring
    rw [regValue_cons' a, regValue_cons' b] at hS
    have step := sum_value_step A B C (regValue (a' :: a'' :: as) s.basis)
      (regValue (b' :: b'' :: bs) s.basis) (n+2)
    have hsb : (sumBit A B C).toNat ≤ 1 := by cases sumBit A B C <;> decide
    have hS' : (2^(n+1) ≤ (regValue (a' :: a'' :: as) s1.basis + regValue (b' :: b'' :: bs) s1.basis +
          (s1.basis c).toNat) % 2^(n+2)) = (r = true) := by
      rw [hxs, hys, hc1, ← hS]
      change (sumBit A B C).toNat + 2 * ((regValue (a' :: a'' :: as) s.basis +
        regValue (b' :: b'' :: bs) s.basis + (carryBit A B C).toNat) % 2^(n+2)) =
        ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
          (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+2+1) at step
      rw [show n+2+1 = n+1+2 by omega] at step
      generalize (regValue (a' :: a'' :: as) s.basis + regValue (b' :: b'' :: bs) s.basis +
        (carryBit A B C).toNat) % 2^(n+2) = S' at step ⊢
      generalize ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
        (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+1+2) = S at step ⊢
      apply propext
      constructor <;> intro h <;> omega
    have hmc : measurementCount (addKT r (a' :: a'' :: as) (b' :: b'' :: bs) cs c) =
        measurementCount (addInPlace (a' :: a'' :: as) (b' :: b'' :: bs) cs c) := by
      rw [(addKT_counts r n _ _ _ c (by simpa using hy) (by simpa using hx)
          (by simpa using hc)).2,
        (addInPlace_counts _ _ _ c (by simpa using hx) (by simpa using hc)).2]
      simp only [List.length_cons] at hy ⊢
      omega
    have hm0 : measurementCount (majority a b cin c) = 0 := rfl
    simp only [addKT, addInPlace, List.cons_ne_nil, if_false]
    rw [List.append_assoc (majority a b cin c ++ _), List.append_assoc (majority a b cin c ++ _)]
    apply run_mid_congr _ _ _ _ m s hm0 hmc
    intro record
    rw [hfirst]
    exact ih _ _ _ c (by simpa using hy) (by simpa using hx) (by simpa using hc) hnd' s1 record
      hclean' hS'


theorem addKT_wires (r : Bool) : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    wires (addKT r x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    intro w hw
    cases r <;> simp [addKT, addInPlace, wires, Instr.wires, majority, eraseCarry] at hw ⊢ <;> tauto
  | succ n ih =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have h := ih (a' :: a'' :: as) (b' :: b'' :: bs) cs c (by simpa using hy)
        (by simpa using hx) (by simpa using hc)
    simp only [addKT, addInPlace, List.cons_ne_nil, if_false, wires_append]
    intro w hw
    simp only [Finset.mem_union] at hw ⊢
    have := @h w
    tauto

theorem addKT_physical (r : Bool) : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    (cin :: (x ++ y ++ carry)).Nodup → GatePhysical (addInPlace x y carry cin) →
    GatePhysical (addKT r x y carry cin) := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc hnd hp
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have ha'c : a' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hb'c : b' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    simp only [addKT, addInPlace, if_pos (rfl : ([] : List Wire) = []), gatePhysical_append] at hp ⊢
    refine ⟨⟨⟨?_, hp.1.1.2⟩, hp.1.2⟩, hp.2⟩
    cases r <;> intro i hi <;> simp at hi <;> rcases hi with rfl | rfl | rfl <;>
      simp [RecordedQuantum.PhysicalInstr, ProperGate, ha'c, hb'c]
  | succ n ih =>
    intro x y carry cin hy hx hc hnd hp
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have hnd' : (c :: ((a' :: a'' :: as) ++ (b' :: b'' :: bs) ++ cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append] at this ⊢; omega
    simp only [addKT, addInPlace, List.cons_ne_nil, if_false, gatePhysical_append] at hp ⊢
    exact ⟨⟨⟨hp.1.1.1, ih _ _ _ c (by simpa using hy) (by simpa using hx) (by simpa using hc) hnd' hp.1.1.2⟩,
      hp.1.2⟩, hp.2⟩

open ECDSAAdd.Entrant.KRegs in
/-- `addHeadI` whose inner adder has the affine top carry. -/
def addHeadIKT (r : Bool) : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::a''::as, b::b'::b''::bs, c::cs, cin =>
      DiagSq.maj0 a b cin c++(addKT r (a'::a''::as) (b'::b''::bs) cs c++eraseCarry a b cin c++[.CX a b,.CX cin b])
  | x, y, c, cin => KRegs.addHeadI x y c cin

theorem addHeadIKT_mc (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h3 : 3 ≤ y.length) :
    measurementCount (addHeadIKT r x y carry cin) = measurementCount (KRegs.addHeadI x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',_|⟨a'',as⟩⟩⟩ <;> rcases y with _|⟨b,_|⟨b',_|⟨b'',bs⟩⟩⟩ <;>
    rcases carry with _|⟨c,cs⟩ <;> simp only [List.length_cons, List.length_nil] at hx hc h3 <;> try omega
  ·
    have k := addKT_counts r as.length (a'::a''::as) (b'::b''::bs) cs c (by simp at hx ⊢; omega)
      (by simp at hx ⊢; omega) (by simp at hx hc ⊢; omega)
    have k2 := addInPlace_counts (a'::a''::as) (b'::b''::bs) cs c (by simp at hx ⊢; omega) (by simp at hc ⊢; omega)
    simp only [addHeadIKT, KRegs.addHeadI, measurementCount_append, k.2, k2.2]
    simp [DiagSq.maj0, measurementCount]
    simp at hx; omega

theorem addHeadIKT_counts (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h3 : 3 ≤ y.length) :
    toffoliCount (addHeadIKT r x y carry cin) + 1 = toffoliCount (KRegs.addHeadI x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',_|⟨a'',as⟩⟩⟩ <;> rcases y with _|⟨b,_|⟨b',_|⟨b'',bs⟩⟩⟩ <;>
    rcases carry with _|⟨c,cs⟩ <;> simp only [List.length_cons, List.length_nil] at hx hc h3 <;> try omega
  ·
    have k := addKT_counts r as.length (a'::a''::as) (b'::b''::bs) cs c (by simp at hx ⊢; omega)
      (by simp at hx ⊢; omega) (by simp at hx hc ⊢; omega)
    have k2 := addInPlace_counts (a'::a''::as) (b'::b''::bs) cs c (by simp at hx ⊢; omega) (by simp at hc ⊢; omega)
    simp only [addHeadIKT, KRegs.addHeadI, toffoliCount_append, k.1, k2.1]
    simp [DiagSq.maj0, toffoliCount, eraseCarry]
    simp at hx; omega

theorem addHeadIKT_run (r : Bool) (n : Nat) (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hy : y.length = n + 3) (hx : x.length = y.length) (hc : carry.length + 1 = y.length)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hcl : ∀ w ∈ carry, s.basis w = false)
    (hi : s.basis cin=false) (h0 : ∀a as,x=a::as → s.basis a=false)
    (hd : ∀a as b bs,x=a::as → y=b::bs → a≠b ∧ a≠cin ∧ b≠cin)
    (hS : (2^(n+2) ≤ (regValue x s.basis + regValue y s.basis + (s.basis cin).toNat) % 2^(n+3)) = (r = true)) :
    run (addHeadIKT r x y carry cin) m s=run (KRegs.addHeadI x y carry cin) m s := by
  rw [KRegs.addHeadI_run x y carry cin m s hi h0 hd,
    ← addKT_eq r (n+1) x y carry cin hy hx hc hn s m hcl hS]
  rcases x with _|⟨a,_|⟨a',_|⟨a'',as⟩⟩⟩ <;> rcases y with _|⟨b,_|⟨b',_|⟨b'',bs⟩⟩⟩ <;>
    rcases carry with _|⟨c,cs⟩ <;> simp only [List.length_cons, List.length_nil] at hx hc hy <;> try omega
  ·
    obtain ⟨h1,-,h3⟩ := hd a _ b _ rfl rfl
    simp only [addHeadIKT, addKT, List.cons_ne_nil, if_false, DiagSq.maj0, majority, List.cons_append, List.nil_append,
      List.append_assoc]
    exact (DiagSq.run_maj_idle a b cin c _ m s hi (by intro h; rw [h0 a _ rfl] at h; cases h) h1 h3).symm

def addLowNC1KT (r : Bool) (x y carry : List Wire) (cin : Wire) : Program :=
  addHeadIKT r x.tail y.tail carry.tail cin ++ [.measureX (carry.headD 0) [] []] ++
    [.CX (x.headD 0) (y.headD 0), .CX cin (y.headD 0)]

def subLowNC1KT (r : Bool) (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addLowNC1KT r x y carry cin ++ notRegister y

theorem tail_nodup (x y carry : List Wire) (cin : Wire) (hn : (cin :: (x ++ y ++ carry)).Nodup) :
    (cin :: (x.tail ++ y.tail ++ carry.tail)).Nodup := by
  exact List.Nodup.sublist (List.Sublist.cons₂ _ (List.Sublist.append (List.Sublist.append (List.tail_sublist x)
    (List.tail_sublist y)) (List.tail_sublist carry))) hn

theorem addLowNC1KT_run (r : Bool) (n : Nat) (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hy : y.tail.length = n + 3) (hx : x.tail.length = y.tail.length) (hc : carry.tail.length + 1 = y.tail.length)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hcl : ∀ w ∈ carry.tail, s.basis w = false)
    (hi : s.basis cin=false) (h1 : s.basis (x.tail.headD 0)=false)
    (hS : (2^(n+2) ≤ (regValue x.tail s.basis + regValue y.tail s.basis) % 2^(n+3)) = (r = true)) :
    run (addLowNC1KT r x y carry cin) m s=run (KRegs.addLowNC1 x y carry cin) m s := by
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
  have e := addHeadIKT_run r n x.tail y.tail carry.tail cin
    (m.take (measurementCount (KRegs.addHeadI x.tail y.tail carry.tail cin))) s hy hx hc
    (tail_nodup x y carry cin hn) hcl hi h0 hd (by rw [hi]; simpa using hS)
  simp only [addLowNC1KT,KRegs.addLowNC1,List.append_assoc]
  rw [run_append (addHeadIKT _ _ _ _ _),run_append (KRegs.addHeadI _ _ _ _),
    addHeadIKT_mc r _ _ _ _ hx hc (by omega),e]

theorem subLowNC1KT_run (r : Bool) (n : Nat) (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hy : y.tail.length = n + 3) (hx : x.tail.length = y.tail.length) (hc : carry.tail.length + 1 = y.tail.length)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hcl : ∀ w ∈ carry.tail, s.basis w = false)
    (hi : s.basis cin=false) (h1 : s.basis (x.tail.headD 0)=false)
    (hS : (2^(n+2) ≤ (regValue x.tail s.basis + (2^(n+3) - 1 - regValue y.tail s.basis)) % 2^(n+3)) = (r = true)) :
    run (subLowNC1KT r x y carry cin) m s=run (KRegs.subLowNC1 x y carry cin) m s := by
  have hm : measurementCount (notRegister y)=0 := (notRegister_counts y).2
  have hyn : y.Nodup := DiagSq.nd_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have nr := notRegister_correct y hyn s []
  have hcy : cin∉y := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hx2 : x.tail.headD 0∉y := by
    have hx1 : x.tail.headD 0∈x := by
      rcases x with _|⟨a,_|⟨b,xs⟩⟩
      · simp at hx hy; omega
      · simp at hx hy; omega
      · simp
    exact DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) _ hx1
  have xty : ∀ q ∈ x.tail, q ∉ y := fun q hq =>
    DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) _ (List.mem_of_mem_tail hq)
  have cty : ∀ q ∈ carry.tail, q ∉ y := fun q hq hqy =>
    DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) _ hqy (List.mem_of_mem_tail hq)
  have ytl : ∀ q ∈ y.tail, q ∈ y := fun q hq => List.mem_of_mem_tail hq
  simp only [subLowNC1KT,KRegs.subLowNC1,List.append_assoc]
  rw [run_append (notRegister y),run_append (notRegister y),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (addLowNC1KT r x y carry cin),
    run_append (KRegs.addLowNC1 x y carry cin),
    show measurementCount (addLowNC1KT r x y carry cin) = measurementCount (KRegs.addLowNC1 x y carry cin) by
      simp only [addLowNC1KT, KRegs.addLowNC1, measurementCount_append, addHeadIKT_mc r _ _ _ _ hx hc (by omega)],
    addLowNC1KT_run r n x y carry cin _ _ hy hx hc hn]
  · intro q hq; rw [nr]; dsimp only; rw [if_neg (cty q hq)]; exact hcl q hq
  · rw [nr]; simp [hcy,hi]
  · rw [nr]; dsimp only; rw [if_neg hx2]; exact h1
  · rw [nr]
    have ex : regValue x.tail (fun w => if w ∈ y then !s.basis w else s.basis w) = regValue x.tail s.basis :=
      regValue_congr _ _ _ (fun q hq => by simp [xty q hq])
    have ey : regValue y.tail (fun w => if w ∈ y then !s.basis w else s.basis w) = 2^y.tail.length - 1 - regValue y.tail s.basis := by
      rw [regValue_congr y.tail _ (fun w => !s.basis w) (fun q hq => by simp [ytl q hq]), regValue_complement]
    dsimp only
    rw [ex, ey, hy]
    exact hS

theorem addKT_slots (r : Bool) : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    Challenge.gateSlots (addKT r x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    cases r <;> simp [addKT, addInPlace, majority, Challenge.gateSlots, Challenge.instructionSlots] <;> omega
  | succ n ih =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have h := ih (a' :: a'' :: as) (b' :: b'' :: bs) cs c (by simpa using hy)
        (by simpa using hx) (by simpa using hc)
    simp only [addKT, addInPlace, List.cons_ne_nil, if_false, Challenge.gateSlots_append]
    omega

theorem addHeadIKT_res (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h3 : 3 ≤ y.length) :
    wires (addHeadIKT r x y carry cin) ⊆ wires (KRegs.addHeadI x y carry cin) ∧
    Challenge.gateSlots (addHeadIKT r x y carry cin) ≤ Challenge.gateSlots (KRegs.addHeadI x y carry cin) ∧
    ((cin :: (x ++ y ++ carry)).Nodup → GatePhysical (KRegs.addHeadI x y carry cin) →
      GatePhysical (addHeadIKT r x y carry cin)) := by
  rcases x with _|⟨a,_|⟨a',_|⟨a'',as⟩⟩⟩ <;> rcases y with _|⟨b,_|⟨b',_|⟨b'',bs⟩⟩⟩ <;>
    rcases carry with _|⟨c,cs⟩ <;> simp only [List.length_cons, List.length_nil] at hx hc h3 <;> try omega
  · have hy : (b'::b''::bs).length = as.length + 2 := by simp at hx ⊢; omega
    have hx' : (a'::a''::as).length = (b'::b''::bs).length := by simp at hx ⊢; omega
    have hc' : cs.length + 1 = (b'::b''::bs).length := by simp at hx hc ⊢; omega
    have kw := addKT_wires r as.length _ _ cs c hy hx' hc'
    have ks := addKT_slots r as.length _ _ cs c hy hx' hc'
    refine ⟨?_, ?_, ?_⟩
    · simp only [addHeadIKT, KRegs.addHeadI, wires_append]
      intro w hw
      simp only [Finset.mem_union] at hw ⊢
      have := @kw w
      tauto
    · simp only [addHeadIKT, KRegs.addHeadI, Challenge.gateSlots_append]
      omega
    · intro hnd hp
      have hcnt := List.nodup_iff_count.mp hnd
      have hnd' : (c :: ((a' :: a'' :: as) ++ (b' :: b'' :: bs) ++ cs)).Nodup := by
        apply List.nodup_iff_count.mpr; intro w; have := hcnt w
        simp only [List.count_cons, List.count_append] at this ⊢; omega
      simp only [addHeadIKT, KRegs.addHeadI, gatePhysical_append] at hp ⊢
      exact ⟨hp.1, ⟨⟨addKT_physical r as.length _ _ cs c hy hx' hc' hnd' hp.2.1.1, hp.2.1.2⟩, hp.2.2⟩⟩

theorem subLowNC1KT_res (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length) :
    toffoliCount (subLowNC1KT r x y carry cin) + 1 = toffoliCount (KRegs.subLowNC1 x y carry cin) ∧
    measurementCount (subLowNC1KT r x y carry cin) = measurementCount (KRegs.subLowNC1 x y carry cin) ∧
    wires (subLowNC1KT r x y carry cin) ⊆ wires (KRegs.subLowNC1 x y carry cin) ∧
    Challenge.gateSlots (subLowNC1KT r x y carry cin) ≤ Challenge.gateSlots (KRegs.subLowNC1 x y carry cin) ∧
    ((cin :: (x ++ y ++ carry)).Nodup → GatePhysical (KRegs.subLowNC1 x y carry cin) →
      GatePhysical (subLowNC1KT r x y carry cin)) := by
  have hx' : x.tail.length = y.tail.length := by simp [hx]
  have hc' : carry.tail.length + 1 = y.tail.length := by simp; omega
  have h3 : 3 ≤ y.tail.length := by simp; omega
  have tc := addHeadIKT_counts r _ _ _ cin hx' hc' h3
  have mc := addHeadIKT_mc r _ _ _ cin hx' hc' h3
  have res := addHeadIKT_res r _ _ _ cin hx' hc' h3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [subLowNC1KT, KRegs.subLowNC1, addLowNC1KT, KRegs.addLowNC1, toffoliCount_append]; omega
  · simp only [subLowNC1KT, KRegs.subLowNC1, addLowNC1KT, KRegs.addLowNC1, measurementCount_append]; omega
  · simp only [subLowNC1KT, KRegs.subLowNC1, addLowNC1KT, KRegs.addLowNC1, wires_append]
    intro w hw
    simp only [Finset.mem_union] at hw ⊢
    have := @res.1 w
    tauto
  · simp only [subLowNC1KT, KRegs.subLowNC1, addLowNC1KT, KRegs.addLowNC1, Challenge.gateSlots_append]
    have := res.2.1; omega
  · intro hnd hp
    simp only [subLowNC1KT, KRegs.subLowNC1, addLowNC1KT, KRegs.addLowNC1, gatePhysical_append] at hp ⊢
    exact ⟨⟨hp.1.1, ⟨res.2.2 (tail_nodup x y carry cin hnd) hp.1.2.1.1, hp.1.2.1.2⟩, hp.1.2.2⟩, hp.2⟩

end ECDSAAdd.Entrant.KnownTop

namespace ECDSAAdd.Entrant.KRegs
open ECDSAAdd ECDSAAdd.Arithmetic
variable (R : KRegs)

theorem regValue_head_tail (l : List Wire) (st : BasisState) (hne : l ≠ []) :
    regValue l st = (st (l.headD 0)).toNat + 2 * regValue l.tail st := by
  match l, hne with
  | w :: ws, _ => exact TopCarry.regValue_cons' w ws st

/-- `m7y` with its top carry made affine: the difference `T - b²` stays below `2^(|T|-1)`. -/
def m7f : Program :=
  if (R.dhi++R.zB).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 4≤R.T.length then
    KnownTop.subLowNC1KT true (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin else R.m7y

theorem m7f_lens (w : R.W) : (R.dhi++R.zB).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 4≤R.T.length := by
  have l := R.t_lensg w
  have h4 := w.h4; have hh := w.hh; have hSl := w.S; have hTl := w.T
  exact ⟨l.1, l.2.1, by omega⟩

theorem m7f_run (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false)
    (hle : regValue (R.dhi++R.zB) s.basis ≤ regValue R.T s.basis)
    (hlt : regValue R.T s.basis < regValue (R.dhi++R.zB) s.basis + 2^(R.T.length-1)) :
    run R.m7f m s=run R.m7y m s := by
  have l := R.t_lensg w
  have l4 := R.m7f_lens w
  unfold m7f m7y
  rw [if_pos l4, if_pos ⟨l.1,l.2.1,l.2.2.1⟩]
  obtain ⟨n, hn4⟩ : ∃ n, R.T.length = n + 4 := ⟨R.T.length - 4, by omega⟩
  have hTne : R.T ≠ [] := fun e => by rw [e] at hn4; simp at hn4
  have hXne : R.dhi++R.zB ≠ [] := fun e => by have := congrArg List.length e; simp only [List.length_nil] at this; omega
  apply KnownTop.subLowNC1KT_run true n _ _ _ _ m s (by simp; omega) (by simp [l.1])
    (by simp only [List.length_tail]; omega)
    (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (fun q hq => hcl q (List.mem_of_mem_tail hq)) hi h1
  refine propext ⟨fun _ => rfl, fun _ => ?_⟩
  rw [regValue_head_tail _ _ hXne] at hle hlt
  rw [regValue_head_tail _ _ hTne] at hle hlt
  have ttl : regValue R.T.tail s.basis < 2^(n+3) := by
    have := regValue_lt R.T.tail s.basis; simp only [List.length_tail] at this; rwa [show R.T.length - 1 = n+3 by omega] at this
  have x0 : (s.basis ((R.dhi++R.zB).headD 0)).toNat ≤ (s.basis (R.T.headD 0)).toNat := by
    revert hnc; cases s.basis ((R.dhi++R.zB).headD 0) <;> cases s.basis (R.T.headD 0) <;> decide
  have t0 : (s.basis (R.T.headD 0)).toNat ≤ 1 := by cases s.basis (R.T.headD 0) <;> decide
  rw [show R.T.length - 1 = n + 3 by omega] at hlt
  have p3 : 2^(n+3) = 2 * 2^(n+2) := by rw [pow_succ]; ring
  rw [p3] at hlt ttl ⊢
  generalize 2^(n+2) = P at hlt ttl ⊢
  generalize regValue R.T.tail s.basis = tt at hle hlt ttl ⊢
  generalize regValue (R.dhi++R.zB).tail s.basis = xt at hle hlt ⊢
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem m7f_res (w : R.W) : toffoliCount R.m7f+1=toffoliCount R.m7y ∧
    measurementCount R.m7f=measurementCount R.m7y ∧ wires R.m7f⊆wires R.m7y ∧
    Challenge.gateSlots R.m7f≤Challenge.gateSlots R.m7y ∧ (R.all.Nodup → GatePhysical R.m7f) := by
  have l := R.t_lensg w
  have l4 := R.m7f_lens w
  have res := KnownTop.subLowNC1KT_res true (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin l4.1 l4.2.1 l4.2.2
  have e1 : R.m7f = KnownTop.subLowNC1KT true (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin := if_pos l4
  have e2 : R.m7y = KRegs.subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin :=
    if_pos ⟨l.1,l.2.1,l.2.2.1⟩
  rw [e1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e2]; exact res.1
  · rw [e2]; exact res.2.1
  · rw [e2]; exact res.2.2.1
  · rw [e2]; exact res.2.2.2.1
  · intro hn
    have hp := R.m7y_physical hn
    rw [e2] at hp
    exact res.2.2.2.2 (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) hp


theorem m7f_counts (w : R.W) : toffoliCount R.m7f+1=toffoliCount R.m7y ∧
    measurementCount R.m7f=measurementCount R.m7y := ⟨(R.m7f_res w).1,(R.m7f_res w).2.1⟩

theorem kt_arith (x0 t0 xt yt Q : Nat) (hx0 : x0 ≤ t0) (ht0 : t0 ≤ 1)
    (hle : x0 + 2*xt ≤ t0 + 2*yt) (hlt : t0 + 2*yt < x0 + 2*xt + 2*Q) (hyt : yt < 2*Q) :
    Q ≤ (xt + (2*Q - 1 - yt)) % (2*Q) := by
  rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `m7t` with its top carry made affine (trimmed register when `trimOK`, full register otherwise). -/
def m7k : Program := if R.topOK then
  KnownTop.subLowNC1KT true ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.m7f

theorem m7k_run (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false)
    (hT : R.trimOK → regValue (R.dhi++R.zB) s.basis<2^(R.T.length-1) ∧
      regValue (R.dhi++R.zB) s.basis≤regValue R.T s.basis%2^(R.T.length-1) ∧
      regValue R.T s.basis%2^(R.T.length-1)<regValue (R.dhi++R.zB) s.basis+2^(R.T.length-2))
    (hF : ¬R.trimOK → regValue (R.dhi++R.zB) s.basis≤regValue R.T s.basis ∧
      regValue R.T s.basis<regValue (R.dhi++R.zB) s.basis+2^(R.T.length-1)) :
    run R.m7k m s=run R.m7t m s := by
  by_cases hc : R.trimOK
  · have top := R.topOK_of w hc
    obtain ⟨hA,hb,hlt⟩ := hT hc
    have e1 : R.m7k=KnownTop.subLowNC1KT true ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos top
    have e2 : R.m7t=subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos top
    obtain ⟨-,h1l,h2,h3⟩ := top
    obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
    have hh4 := w.h4; have hSl := w.S; have hTl := w.T
    have hc' : 2*R.h+1≤R.bank.length := hc
    obtain ⟨n, hn5⟩ : ∃ n, R.T.length = n + 6 := ⟨R.T.length - 6, by omega⟩
    rw [e1,e2]
    apply KnownTop.subLowNC1KT_run true (n+1) _ _ _ _ m s (by simp only [List.length_tail,List.length_take]; omega)
      (by simp only [List.length_tail,List.length_take]; omega) (by simp only [List.length_tail,List.length_take] at h2 ⊢; omega)
      (R.top_nodup hn) (fun q hq => hcl q (List.mem_of_mem_take (List.mem_of_mem_tail hq))) hi
      (by rw [take_tail_headD _ _ (by omega)]; exact h1)
    refine propext ⟨fun _ => rfl, fun _ => ?_⟩
    have xne : (R.dhi++R.zB).take (R.T.length-1)≠[] := by
      intro e; have := congrArg List.length e; simp only [List.length_take,List.length_nil] at this; omega
    have yne : R.T.take (R.T.length-1)≠[] := by
      intro e; have := congrArg List.length e; simp only [List.length_take,List.length_nil] at this; omega
    have xv : regValue ((R.dhi++R.zB).take (R.T.length-1)) s.basis=regValue (R.dhi++R.zB) s.basis := by
      rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega),Nat.mod_eq_of_lt hA]
    have yv : regValue (R.T.take (R.T.length-1)) s.basis=regValue R.T s.basis%2^(R.T.length-1) :=
      CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega) _
    have xh := regValue_head_tail _ s.basis xne
    have yh := regValue_head_tail _ s.basis yne
    rw [take_headD _ _ (by omega)] at xh yh
    rw [xv] at xh; rw [yv] at yh
    have ttl : regValue (R.T.take (R.T.length-1)).tail s.basis<2^(n+1+3) := by
      have := regValue_lt (R.T.take (R.T.length-1)).tail s.basis
      simp only [List.length_tail,List.length_take] at this
      rwa [show min (R.T.length-1) R.T.length-1=n+1+3 by omega] at this
    have x0 : (s.basis ((R.dhi++R.zB).headD 0)).toNat ≤ (s.basis (R.T.headD 0)).toNat := by
      revert hnc; cases s.basis ((R.dhi++R.zB).headD 0) <;> cases s.basis (R.T.headD 0) <;> decide
    have t0 : (s.basis (R.T.headD 0)).toNat ≤ 1 := by cases s.basis (R.T.headD 0) <;> decide
    have p3 : 2^(n+1+3)=2*2^(n+1+2) := by rw [show n+1+3=(n+1+2)+1 by omega,pow_succ]; ring
    have pl : 2^(R.T.length-2)=2^(n+1+3) := by congr 1; omega
    rw [pl] at hlt
    rw [p3] at ttl hlt ⊢
    exact kt_arith _ _ _ _ _ x0 t0 (by omega) (by omega) ttl
  · have e1 : R.m7k=R.m7f := if_neg (fun h => hc h.1)
    have e2 : R.m7t=R.m7y := if_neg (fun h => hc h.1)
    rw [e1,e2]
    exact R.m7f_run w hn s m hcl hnc hi h1 (hF hc).1 (hF hc).2

theorem m7k_res (w : R.W) : toffoliCount R.m7k+1=toffoliCount R.m7t ∧
    measurementCount R.m7k=measurementCount R.m7t ∧ wires R.m7k⊆wires R.m7t ∧
    Challenge.gateSlots R.m7k≤Challenge.gateSlots R.m7t ∧ (R.all.Nodup → GatePhysical R.m7k) := by
  by_cases hc : R.trimOK
  · have top := R.topOK_of w hc
    have e1 : R.m7k=KnownTop.subLowNC1KT true ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos top
    have e2 : R.m7t=subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos top
    obtain ⟨-,h1l,h2,h3⟩ := top
    obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
    have hh4 := w.h4; have hSl := w.S; have hTl := w.T
    have hc' : 2*R.h+1≤R.bank.length := hc
    have res := KnownTop.subLowNC1KT_res true ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin
        (by simp only [List.length_take]; omega) (by simp only [List.length_take] at h2 ⊢; omega)
        (by simp only [List.length_take]; omega)
    rw [e1,e2]
    refine ⟨res.1,res.2.1,res.2.2.1,res.2.2.2.1,fun hn => ?_⟩
    have hp := R.m7t_physical hn
    rw [e2] at hp
    exact res.2.2.2.2 (R.top_nodup hn) hp
  · have e1 : R.m7k=R.m7f := if_neg (fun h => hc h.1)
    have e2 : R.m7t=R.m7y := if_neg (fun h => hc h.1)
    rw [e1,e2]
    exact R.m7f_res w

theorem m7k_counts (w : R.W) : toffoliCount R.m7k+1=toffoliCount R.m7t ∧
    measurementCount R.m7k=measurementCount R.m7t := ⟨(R.m7k_res w).1,(R.m7k_res w).2.1⟩
theorem m7k_wires (w : R.W) : wires R.m7k⊆wires R.m7 := (R.m7k_res w).2.2.1.trans R.m7t_wires
theorem m7k_slots (w : R.W) : Challenge.gateSlots R.m7k≤Challenge.gateSlots R.m7 :=
  (R.m7k_res w).2.2.2.1.trans R.m7t_slots
theorem m7k_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.m7k := (R.m7k_res w).2.2.2.2 hn

end ECDSAAdd.Entrant.KRegs
end

end

-- Research extension: m6 second and high carry; full integration pending.
section

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Entrant.CodexM6Carry
open ECDSAAdd ECDSAAdd.Arithmetic

/-- Keep ConstCarry's second-majority reduction and replace the independent
    final majority using KnownTop. At least four bits separates the two sites. -/
def addInPlace2KT (r : Bool) : List Wire → List Wire → List Wire → Wire → Program
  | a0 :: a1 :: a2 :: a3 :: as, b0 :: b1 :: b2 :: b3 :: bs, c0 :: c1 :: cs, cin =>
      majority a0 b0 cin c0 ++
        ([.CX c0 c1] ++ KnownTop.addKT r (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1 ++
          eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++
        eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0]
  | x, y, c, cin => ConstCarry.addInPlace2 x y c cin

def subInPlace2KT (r : Bool) (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addInPlace2KT r x y carry cin ++ notRegister y

theorem addKT_shape4 (r : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 cin : Wire)
    (as bs cs : List Wire) :
    KnownTop.addKT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin =
      majority a0 b0 cin c0 ++
        (majority a1 b1 c0 c1 ++ KnownTop.addKT r (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1 ++
          eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++
        eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0] := by
  simp only [KnownTop.addKT, List.cons_ne_nil, if_false]

/-- This local rewrite needs no top-bit hypothesis: both programs use the same
    KnownTop tail; only the second majority is compared. -/
theorem addInPlace2KT_run (r : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 cin : Wire)
    (as bs cs : List Wire)
    (h0 : [a0, b0, cin, c0].Nodup) (h1 : [a1, b1, c0, c1].Nodup)
    (ha : a1 ≠ c0) (hb : b1 ≠ c0) (s : State) (m : List Bool)
    (h : s.basis a1 ≠ s.basis b1) :
    run (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) m s =
    run (KnownTop.addKT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) m s := by
  rw [addKT_shape4]
  simp only [addInPlace2KT, List.append_assoc]
  rw [ConstCarry.run_pre _ _ (ConstCarry.majority_mc _ _ _ _),
    ConstCarry.run_pre _ _ (ConstCarry.majority_mc _ _ _ _),
    ConstCarry.run_pre [.CX c0 c1] _ (by simp [measurementCount]),
    ConstCarry.run_pre _ _ (ConstCarry.majority_mc _ _ _ _)]
  congr 1
  have t := majority_correct a0 b0 cin c0 h0 s []
  have e := ConstCarry.majority_ne a1 b1 c0 c1 h1
    (run (majority a0 b0 cin c0) [] s) (by
      rw [t]; simpa [writeBit, Function.update, ha, hb] using h)
  exact e.symm

theorem addInPlace2KT_counts_shape (r : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 cin : Wire) (as bs cs : List Wire)
    (hx : as.length = bs.length) (hc : cs.length + 1 = bs.length + 2) :
    toffoliCount (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) + 1 =
      toffoliCount (ConstCarry.addInPlace2 (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) ∧
    measurementCount (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) =
      measurementCount (ConstCarry.addInPlace2 (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) := by
  have kt := KnownTop.addKT_counts r as.length (a2 :: a3 :: as)
    (b2 :: b3 :: bs) cs c1 (by simp; omega) (by simp; omega) (by simp; omega)
  have old := addInPlace_counts (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1
    (by simp; omega) (by simp; omega)
  simp only [List.length_cons] at old
  simp only [addInPlace2KT, ConstCarry.addInPlace2,
    toffoliCount_append, measurementCount_append]
  constructor <;> omega

theorem addInPlace2KT_counts (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length) :
    toffoliCount (addInPlace2KT r x y carry cin) + 1 =
      toffoliCount (ConstCarry.addInPlace2 x y carry cin) ∧
    measurementCount (addInPlace2KT r x y carry cin) =
      measurementCount (ConstCarry.addInPlace2 x y carry cin) := by
  rcases x with _|⟨a0,_|⟨a1,_|⟨a2,_|⟨a3,as⟩⟩⟩⟩ <;>
    rcases y with _|⟨b0,_|⟨b1,_|⟨b2,_|⟨b3,bs⟩⟩⟩⟩ <;>
    rcases carry with _|⟨c0,_|⟨c1,cs⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hx hc h4 <;> try omega
  exact addInPlace2KT_counts_shape r _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)

theorem subInPlace2KT_counts (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length) :
    toffoliCount (subInPlace2KT r x y carry cin) + 1 =
      toffoliCount (ConstCarry.subInPlace2 x y carry cin) ∧
    measurementCount (subInPlace2KT r x y carry cin) =
      measurementCount (ConstCarry.subInPlace2 x y carry cin) := by
  have h := addInPlace2KT_counts r x y carry cin hx hc h4
  simp only [subInPlace2KT, ConstCarry.subInPlace2,
    toffoliCount_append, measurementCount_append]
  constructor <;> omega

theorem addInPlace2KT_res_shape (r : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 cin : Wire) (as bs cs : List Wire)
    (hx : as.length = bs.length) (hc : cs.length + 1 = bs.length + 2) :
    wires (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) ⊆
      wires (ConstCarry.addInPlace2 (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) ∧
    Challenge.gateSlots (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) ≤
      Challenge.gateSlots (ConstCarry.addInPlace2 (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) ∧
    ((cin :: ((a0 :: a1 :: a2 :: a3 :: as) ++
        (b0 :: b1 :: b2 :: b3 :: bs) ++ (c0 :: c1 :: cs))).Nodup →
      GatePhysical (ConstCarry.addInPlace2 (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) →
      GatePhysical (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin)) := by
  have hy' : (b2 :: b3 :: bs).length = as.length + 2 := by simp; omega
  have hx' : (a2 :: a3 :: as).length = (b2 :: b3 :: bs).length := by simp; omega
  have hc' : cs.length + 1 = (b2 :: b3 :: bs).length := by simp; omega
  have kw := KnownTop.addKT_wires r as.length (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1 hy' hx' hc'
  have ks := KnownTop.addKT_slots r as.length (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1 hy' hx' hc'
  refine ⟨?_, ?_, ?_⟩
  · simp only [addInPlace2KT, ConstCarry.addInPlace2, wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    have := @kw q
    tauto
  · simp only [addInPlace2KT, ConstCarry.addInPlace2, Challenge.gateSlots_append]
    omega
  · intro hn hp
    have hcnt := List.nodup_iff_count_le_one.mp hn
    have hnt : (c1 :: ((a2 :: a3 :: as) ++ (b2 :: b3 :: bs) ++ cs)).Nodup := by
      apply List.nodup_iff_count_le_one.mpr
      intro q
      have := hcnt q
      simp only [List.count_cons, List.count_append] at this ⊢
      omega
    have hpt : GatePhysical (addInPlace (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1) := by
      simp only [ConstCarry.addInPlace2, gatePhysical_append] at hp
      tauto
    have hnew := KnownTop.addKT_physical r as.length (a2 :: a3 :: as)
      (b2 :: b3 :: bs) cs c1 hy' hx' hc' hnt hpt
    simp only [addInPlace2KT, ConstCarry.addInPlace2, gatePhysical_append] at hp ⊢
    tauto

theorem addInPlace2KT_res (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length) :
    wires (addInPlace2KT r x y carry cin) ⊆ wires (ConstCarry.addInPlace2 x y carry cin) ∧
    Challenge.gateSlots (addInPlace2KT r x y carry cin) ≤
      Challenge.gateSlots (ConstCarry.addInPlace2 x y carry cin) ∧
    ((cin :: (x ++ y ++ carry)).Nodup → GatePhysical (ConstCarry.addInPlace2 x y carry cin) →
      GatePhysical (addInPlace2KT r x y carry cin)) := by
  rcases x with _|⟨a0,_|⟨a1,_|⟨a2,_|⟨a3,as⟩⟩⟩⟩ <;>
    rcases y with _|⟨b0,_|⟨b1,_|⟨b2,_|⟨b3,bs⟩⟩⟩⟩ <;>
    rcases carry with _|⟨c0,_|⟨c1,cs⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hx hc h4 <;> try omega
  exact addInPlace2KT_res_shape r _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)

theorem subInPlace2KT_res (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length) :
    wires (subInPlace2KT r x y carry cin) ⊆ wires (ConstCarry.subInPlace2 x y carry cin) ∧
    Challenge.gateSlots (subInPlace2KT r x y carry cin) ≤
      Challenge.gateSlots (ConstCarry.subInPlace2 x y carry cin) ∧
    ((cin :: (x ++ y ++ carry)).Nodup → GatePhysical (ConstCarry.subInPlace2 x y carry cin) →
      GatePhysical (subInPlace2KT r x y carry cin)) := by
  have h := addInPlace2KT_res r x y carry cin hx hc h4
  refine ⟨?_, ?_, ?_⟩
  · simp only [subInPlace2KT, ConstCarry.subInPlace2, wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h.1)
      (Finset.Subset.refl _)
  · have hs := h.2.1
    simp only [subInPlace2KT, ConstCarry.subInPlace2, Challenge.gateSlots_append]
    omega
  · intro hn hp
    simp only [subInPlace2KT, ConstCarry.subInPlace2, gatePhysical_append] at hp ⊢
    have ha : GatePhysical (ConstCarry.addInPlace2 x y carry cin) := by tauto
    have hnw := h.2.2 hn ha
    tauto

/-- Reuse the existing full-register KnownTop proof after rewriting only the
    low second majority. The final notRegister restores the subtraction domain. -/
theorem subInPlace2KT_run (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length)
    (s : State) (m : List Bool) (hclean : ∀ q ∈ carry, s.basis q = false)
    (hi : s.basis cin = false)
    (hb : s.basis (y.getD 1 0) = s.basis (x.getD 1 0))
    (hS : (2^(y.length - 1) ≤
      (regValue x s.basis + (2^y.length - 1 - regValue y s.basis)) % 2^y.length) = (r = true)) :
    run (subInPlace2KT r x y carry cin) m s = run (subInPlace x y carry cin) m s := by
  rcases x with _|⟨a0,_|⟨a1,_|⟨a2,_|⟨a3,as⟩⟩⟩⟩ <;>
    rcases y with _|⟨b0,_|⟨b1,_|⟨b2,_|⟨b3,bs⟩⟩⟩⟩ <;>
    rcases carry with _|⟨c0,_|⟨c1,cs⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hx hc h4 <;> try omega
  have hnfull := hn
  have hyn : (b0 :: b1 :: b2 :: b3 :: bs).Nodup :=
    DiagSq.nd_count hn (fun q => by simp only [List.count_cons, List.count_append]; omega)
  have xny : ∀ q ∈ a0 :: a1 :: a2 :: a3 :: as, q ∉ b0 :: b1 :: b2 :: b3 :: bs :=
    DiagSq.dis_count hn (fun q => by simp only [List.count_cons, List.count_append]; omega)
  have cny : ∀ q ∈ c0 :: c1 :: cs, q ∉ b0 :: b1 :: b2 :: b3 :: bs := by
    intro q hq hqy
    exact DiagSq.dis_count hn (fun q => by simp only [List.count_cons, List.count_append]; omega) q hqy hq
  have cinny : cin ∉ b0 :: b1 :: b2 :: b3 :: bs := by
    intro h
    exact (List.nodup_cons.mp hn).1 (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))))
  have nr := notRegister_correct (b0 :: b1 :: b2 :: b3 :: bs) hyn s []
  have mz := ConstCarry.notRegister_mc (b0 :: b1 :: b2 :: b3 :: bs)
  have mnew := addInPlace2KT_counts r (a0 :: a1 :: a2 :: a3 :: as)
    (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin
    (by simpa using hx) (by simpa using hc) (by simp)
  have mold := ConstCarry.addInPlace2_counts a0 a1 a2 b0 b1 b2 c0 c1 cin
    (a3 :: as) (b3 :: bs) cs
  have mc : measurementCount (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) =
      measurementCount (addInPlace (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) := mnew.2.trans mold.2
  simp only [subInPlace2KT, subInPlace, List.append_assoc]
  rw [ConstCarry.run_pre _ _ mz, ConstCarry.run_pre _ _ mz,
    run_append, run_append (addInPlace _ _ _ _), mc]
  congr 1
  calc
    _ = run (KnownTop.addKT r (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) _
        (run (notRegister (b0 :: b1 :: b2 :: b3 :: bs)) [] s) := by
      apply addInPlace2KT_run
      · exact DiagSq.nd_count hn (fun q => by
          simp only [List.count_cons, List.count_nil, List.count_append]; omega)
      · exact DiagSq.nd_count hn (fun q => by
          simp only [List.count_cons, List.count_nil, List.count_append]; omega)
      · intro he
        have hd := DiagSq.dis_count (r := [a1]) (t := [c0]) hn (fun q => by
          simp only [List.count_cons, List.count_nil, List.count_append]; omega) a1 (by simp)
        exact hd (by simpa using he)
      · intro he
        have hd := DiagSq.dis_count (r := [b1]) (t := [c0]) hn (fun q => by
          simp only [List.count_cons, List.count_nil, List.count_append]; omega) b1 (by simp)
        exact hd (by simpa using he)
      · rw [nr]
        simp only [List.getD_cons_succ, List.getD_cons_zero] at hb
        dsimp only
        rw [if_neg (xny a1 (by simp)), if_pos (by simp : b1 ∈ b0 :: b1 :: b2 :: b3 :: bs), hb]
        cases s.basis a1 <;> decide
    _ = _ := by
      apply KnownTop.addKT_eq r (bs.length + 2) _ _ _ _
        (by simp) (by simpa using hx) (by simpa using hc) hnfull
      · intro q hq
        rw [nr]
        dsimp only
        rw [if_neg (cny q hq)]
        exact hclean q hq
      · rw [nr]
        have ex : regValue (a0 :: a1 :: a2 :: a3 :: as)
            (fun q => if q ∈ b0 :: b1 :: b2 :: b3 :: bs then !s.basis q else s.basis q) =
            regValue (a0 :: a1 :: a2 :: a3 :: as) s.basis :=
          regValue_congr _ _ _ (fun q hq => by simp [xny q hq])
        have ey : regValue (b0 :: b1 :: b2 :: b3 :: bs)
            (fun q => if q ∈ b0 :: b1 :: b2 :: b3 :: bs then !s.basis q else s.basis q) =
            2^(b0 :: b1 :: b2 :: b3 :: bs).length - 1 -
              regValue (b0 :: b1 :: b2 :: b3 :: bs) s.basis := by
          rw [regValue_congr _ _ (fun q => !s.basis q) (fun q hq => by simp [hq]),
            regValue_complement]
        dsimp only
        rw [ex, ey, if_neg cinny, hi, Bool.toNat_false, Nat.add_zero]
        simpa [List.length_cons, Nat.add_assoc] using hS

/-- Numeric top-bit condition for subtraction's complemented add domain.
    Unlike m7's low-no-carry wrapper, m6 uses the full register, so no head/tail
    division or low-bit no-borrow lemma is needed here. -/
theorem sub_top (x y n : Nat) (hy : y < 2^(n+1))
    (hle : x ≤ y) (hlt : y < x + 2^n) :
    2^n ≤ (x + (2^(n+1) - 1 - y)) % 2^(n+1) := by
  have hp : 2^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
  rw [hp] at hy ⊢
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

end ECDSAAdd.Entrant.CodexM6Carry



set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Entrant.KRegs
open ECDSAAdd ECDSAAdd.Arithmetic

/-- Only the 129-bit outer leaf uses this branch. The 128-bit leaves retain m6c. -/
def m6k (R : KRegs) : Program :=
  if R.trimOK then CodexM6Carry.subInPlace2KT true (R.dlo ++ R.zA) R.T
    (R.carry.take (R.T.length - 1)) R.cin else R.m6c

theorem m6k_lens (R : KRegs) (w : R.W) :
    (R.dlo ++ R.zA).length = R.T.length ∧
    (R.carry.take (R.T.length - 1)).length + 1 = R.T.length ∧ 4 ≤ R.T.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have hSl := w.S
  have hTl := w.T; have hcl := w.carry
  simp only [List.length_append, List.length_take]
  omega

theorem m6k_counts (R : KRegs) (w : R.W) :
    toffoliCount R.m6k + (if R.trimOK then 1 else 0) = toffoliCount R.m6c ∧
    measurementCount R.m6k = measurementCount R.m6c := by
  have l := m6k_lens R w
  by_cases ht : R.trimOK
  · simp only [m6k, if_pos ht]
    exact CodexM6Carry.subInPlace2KT_counts true _ _ _ _ l.1 l.2.1 l.2.2
  · simp only [m6k, if_neg ht, Nat.add_zero, and_self]

theorem m6k_wires (R : KRegs) (w : R.W) : wires R.m6k ⊆ wires R.m6 := by
  have l := R.m6k_lens w
  by_cases ht : R.trimOK
  · simp only [m6k, if_pos ht]
    exact (CodexM6Carry.subInPlace2KT_res true _ _ _ _ l.1 l.2.1 l.2.2).1.trans
      (R.m6c_wires w)
  · simpa only [m6k, if_neg ht] using R.m6c_wires w

theorem m6k_slots (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.m6k ≤ Challenge.gateSlots R.m6 := by
  have l := R.m6k_lens w
  by_cases ht : R.trimOK
  · simp only [m6k, if_pos ht]
    exact (CodexM6Carry.subInPlace2KT_res true _ _ _ _ l.1 l.2.1 l.2.2).2.1.trans
      (R.m6c_slots w)
  · simpa only [m6k, if_neg ht] using R.m6c_slots w

theorem m6k_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (hp : GatePhysical R.m6) : GatePhysical R.m6k := by
  have l := R.m6k_lens w
  have old := R.m6c_physical w (R.carry_take_nodup hn _) hp
  by_cases ht : R.trimOK
  · simp only [m6k, if_pos ht]
    exact (CodexM6Carry.subInPlace2KT_res true _ _ _ _ l.1 l.2.1 l.2.2).2.2
      (knd hn (fun q => by
        have c := R.counts q
        simp only [KRegs.all, List.count_cons, List.count_append] at c ⊢
        omega)) old
  · simpa only [m6k, if_neg ht] using old

/-- Drop-in replacement for the existing st6 rewrite, with clean carries and
    the conditional half-range bound that make_correct already proves. -/
theorem m6k_run (R : KRegs) (w : R.W)
    (hn : (R.cin :: ((R.dlo ++ R.zA) ++ R.T ++ R.carry.take (R.T.length - 1))).Nodup)
    (s : State) (m : List Bool)
    (hclean : ∀ q ∈ R.carry.take (R.T.length - 1), s.basis q = false)
    (hi : s.basis R.cin = false)
    (hb : s.basis (R.T.getD 1 0) = s.basis (R.dlo.getD 1 0))
    (hbound : R.trimOK → regValue (R.dlo ++ R.zA) s.basis ≤ regValue R.T s.basis ∧
      regValue R.T s.basis < regValue (R.dlo ++ R.zA) s.basis + 2^(R.T.length - 1)) :
    run R.m6k m s = run R.m6 m s := by
  by_cases ht : R.trimOK
  · have l := R.m6k_lens w
    have ml := R.m6c_lens w
    obtain ⟨hle, hlt⟩ := hbound ht
    simp only [m6k, if_pos ht, m6]
    apply CodexM6Carry.subInPlace2KT_run true _ _ _ _ hn l.1 l.2.1 l.2.2
      s m hclean hi
    · rw [hb, List.getD_append _ _ _ _ (by omega)]
    · refine propext ⟨fun _ => rfl, fun _ => ?_⟩
      have htlen : R.T.length - 1 + 1 = R.T.length := by omega
      have htv := regValue_lt R.T s.basis
      have h := CodexM6Carry.sub_top (regValue (R.dlo ++ R.zA) s.basis)
        (regValue R.T s.basis) (R.T.length - 1) (by simpa [htlen] using htv) hle hlt
      simpa [htlen] using h
  · simp only [m6k, if_neg ht]
    exact R.m6c_run w hn s m hb

/-- The concrete square-state premises already available before m6. -/
theorem m6k_square_run (R : KRegs) (w : R.W)
    (hn : (R.cin :: ((R.dlo ++ R.zA) ++ R.T ++ R.carry.take (R.T.length - 1))).Nodup)
    (s : State) (m : List Bool)
    (hclean : ∀ q ∈ R.carry.take (R.T.length - 1), s.basis q = false)
    (hi : s.basis R.cin = false)
    (a b : Nat) (ha : a < 2^R.h) (hb : b < 2^(R.bank.length-R.h))
    (hT : regValue R.T s.basis = (a+b)^2)
    (hA : regValue R.dlo s.basis = a^2)
    (hz : regValue R.zA s.basis = 0) :
    run R.m6k m s = run R.m6 m s := by
  apply R.m6k_run w hn s m hclean hi (R.m6c_bits w s.basis (a+b) a hT hA)
  intro ht
  have hx : regValue (R.dlo ++ R.zA) s.basis = a^2 := by
    rw [regValue_append, hA, hz, Nat.mul_zero, Nat.add_zero]
  have hp := trim_bound R.bank.length R.h a b ht ha hb
  have hTl := w.T
  have hSl := w.S
  rw [hx, hT, hTl, hSl]
  have ex : (a+b)^2 = a^2 + (2*a*b+b^2) := by ring
  rw [ex]
  constructor <;> omega

end ECDSAAdd.Entrant.KRegs

end

-- Affine first m6 carry: checked generic and actual KRegs components.
section

set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.CodexM6AffineHead
open ECDSAAdd ECDSAAdd.Arithmetic

def bit0 (n : Nat) : Bool := decide (n % 2 = 1)
def bit1 (n : Nat) : Bool := decide (n / 2 % 2 = 1)

theorem bit0_square (n : Nat) : bit0 (n^2) = bit0 n := by
  have hm := Nat.mod_lt n (by decide : 0 < 2)
  have he := Nat.pow_mod n 2 2
  unfold bit0
  rw [he]
  interval_cases n % 2 <;> norm_num

theorem head_sum_formula (a b : Nat) :
    (bit0 a && !bit0 (a+b)) = ((bit1 (a+b) ^^ bit1 a) ^^ bit1 b) := by
  unfold bit0 bit1
  have ha := Nat.mod_lt a (by decide : 0 < 2)
  have hb := Nat.mod_lt b (by decide : 0 < 2)
  have hs := Nat.mod_lt (a+b) (by decide : 0 < 2)
  have ha1 := Nat.mod_lt (a/2) (by decide : 0 < 2)
  have hb1 := Nat.mod_lt (b/2) (by decide : 0 < 2)
  have hs1 := Nat.mod_lt ((a+b)/2) (by decide : 0 < 2)
  by_cases a0 : a % 2 = 1 <;> by_cases b0 : b % 2 = 1 <;>
    by_cases s0 : (a+b) % 2 = 1 <;> by_cases a1 : a/2 % 2 = 1 <;>
    by_cases b1 : b/2 % 2 = 1 <;> by_cases s1 : (a+b)/2 % 2 = 1 <;>
    simp_all <;> omega

theorem square_head_formula (a b : Nat) :
    carryBit (bit0 (a^2)) (!bit0 ((a+b)^2)) false =
      ((bit1 (a+b) ^^ bit1 a) ^^ bit1 b) := by
  rw [bit0_square, bit0_square]
  simpa [carryBit] using head_sum_formula a b

def program (u v w c : Wire) : Program := [.CX u c, .CX v c, .CX w c]

theorem program_run (u v w c : Wire) (_hu : u ≠ c) (hv : v ≠ c) (hw : w ≠ c)
    (s : State) (m : List Bool) :
    run (program u v w c) m s =
      ⟨s.phase, writeBit s.basis c (s.basis c ^^ ((s.basis u ^^ s.basis v) ^^ s.basis w))⟩ := by
  simp only [program, run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = c <;>
    simp_all [writeBit, Function.update]

theorem majority_eq (a b cin c u v w : Wire)
    (hn : [a,b,cin,c].Nodup) (hu : u ≠ c) (hv : v ≠ c) (hw : w ≠ c)
    (s : State) (m : List Bool)
    (hcarry : carryBit (s.basis a) (s.basis b) (s.basis cin) =
      ((s.basis u ^^ s.basis v) ^^ s.basis w)) :
    run (program u v w c) m s = run (majority a b cin c) m s := by
  rw [program_run u v w c hu hv hw, majority_correct a b cin c hn, hcarry]

theorem counts (u v w c : Wire) :
    toffoliCount (program u v w c) = 0 ∧ measurementCount (program u v w c) = 0 := by
  simp [program, toffoliCount, measurementCount]

theorem physical (u v w c : Wire) (hu : u ≠ c) (hv : v ≠ c) (hw : w ≠ c) :
    GatePhysical (program u v w c) := by
  simp [program, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hu, hv, hw]

end ECDSAAdd.Entrant.CodexM6AffineHead


set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.CodexM6AffineHead
open ECDSAAdd ECDSAAdd.Arithmetic

def replaceHead (p : Program) (u v w c : Wire) : Program :=
  program u v w c ++ p.drop 6

theorem replaceHead_shape (a b cin c u v w : Wire) (tail : Program) :
    replaceHead (majority a b cin c ++ tail) u v w c = program u v w c ++ tail := by
  simp [replaceHead, majority]

theorem replaceHead_run (a b cin c u v w : Wire) (tail : Program)
    (hn : [a,b,cin,c].Nodup) (hu : u ≠ c) (hv : v ≠ c) (hw : w ≠ c)
    (s : State) (m : List Bool)
    (hcarry : carryBit (s.basis a) (s.basis b) (s.basis cin) =
      ((s.basis u ^^ s.basis v) ^^ s.basis w)) :
    run (replaceHead (majority a b cin c ++ tail) u v w c) m s =
      run (majority a b cin c ++ tail) m s := by
  rw [replaceHead_shape,
    ConstCarry.run_pre _ _ (counts u v w c).2,
    ConstCarry.run_pre _ _ (ConstCarry.majority_mc a b cin c),
    majority_eq a b cin c u v w hn hu hv hw s [] hcarry]

theorem replaceHead_counts (a b cin c u v w : Wire) (tail : Program) :
    toffoliCount (replaceHead (majority a b cin c ++ tail) u v w c) + 1 =
      toffoliCount (majority a b cin c ++ tail) ∧
    measurementCount (replaceHead (majority a b cin c ++ tail) u v w c) =
      measurementCount (majority a b cin c ++ tail) := by
  rw [replaceHead_shape]
  simp [program, majority, toffoliCount, measurementCount, Nat.add_comm]

theorem replaceHead_slots (a b cin c u v w : Wire) (tail : Program) :
    Challenge.gateSlots (replaceHead (majority a b cin c ++ tail) u v w c) ≤
      Challenge.gateSlots (majority a b cin c ++ tail) := by
  rw [replaceHead_shape]
  simp [program, majority, Challenge.gateSlots, Challenge.instructionSlots]
  omega

theorem replaceHead_wires (a b cin c u v w : Wire) (tail : Program) :
    wires (replaceHead (majority a b cin c ++ tail) u v w c) ⊆
      wires (majority a b cin c ++ tail) ∪ {u,v,w} := by
  simp only [replaceHead_shape, wires_append]
  intro q hq
  simp [program, majority, wires, Instr.wires] at hq ⊢
  tauto

theorem replaceHead_physical (a b cin c u v w : Wire) (tail : Program)
    (hu : u ≠ c) (hv : v ≠ c) (hw : w ≠ c)
    (hp : GatePhysical (majority a b cin c ++ tail)) :
    GatePhysical (replaceHead (majority a b cin c ++ tail) u v w c) := by
  rw [replaceHead_shape, gatePhysical_append]
  exact ⟨physical u v w c hu hv hw, ((gatePhysical_append _ _).mp hp).2⟩

def addBase (top : Bool) (x y carry : List Wire) (cin : Wire) : Program :=
  if top then CodexM6Carry.addInPlace2KT true x y carry cin
  else ConstCarry.addInPlace2 x y carry cin

theorem addBase_shape (top : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 cin : Wire)
    (as bs cs : List Wire) :
    ∃ tail, addBase top (a0::a1::a2::a3::as) (b0::b1::b2::b3::bs) (c0::c1::cs) cin =
      majority a0 b0 cin c0 ++ tail := by
  cases top <;> simp only [addBase, Bool.false_eq_true, if_false, if_true,
    CodexM6Carry.addInPlace2KT, ConstCarry.addInPlace2, List.append_assoc] <;> exact ⟨_, rfl⟩


theorem addBase_has_head (top : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length) :
    ∃ tail, addBase top x y carry cin =
      majority (x.getD 0 0) (y.getD 0 0) cin (carry.getD 0 0) ++ tail := by
  rcases x with _|⟨a0,_|⟨a1,_|⟨a2,_|⟨a3,as⟩⟩⟩⟩ <;>
    rcases y with _|⟨b0,_|⟨b1,_|⟨b2,_|⟨b3,bs⟩⟩⟩⟩ <;>
    rcases carry with _|⟨c0,_|⟨c1,cs⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hx hy hc <;> try omega
  exact addBase_shape top _ _ _ _ _ _ _ _ _ _ _ _ _ _

def subAffine (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ replaceHead (addBase top x y carry cin) u v w (carry.getD 0 0) ++
    notRegister y

theorem subAffine_run (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length)
    (hn : [x.getD 0 0, y.getD 0 0, cin, carry.getD 0 0].Nodup) (hyn : y.Nodup)
    (hxn : x.getD 0 0 ∉ y) (hin : cin ∉ y)
    (hun : u ∉ y) (hvn : v ∉ y) (hwn : w ∉ y)
    (hu : u ≠ carry.getD 0 0) (hv : v ≠ carry.getD 0 0) (hw : w ≠ carry.getD 0 0)
    (s : State) (m : List Bool)
    (hcarry : carryBit (s.basis (x.getD 0 0)) (!s.basis (y.getD 0 0)) (s.basis cin) =
      ((s.basis u ^^ s.basis v) ^^ s.basis w)) :
    run (subAffine top u v w x y carry cin) m s =
      run (notRegister y ++ addBase top x y carry cin ++ notRegister y) m s := by
  obtain ⟨tail, he⟩ := addBase_has_head top x y carry cin hx hy hc
  have hy0 : y.getD 0 0 ∈ y := by
    cases y with
    | nil => simp at hy
    | cons b bs => simp
  have hct := replaceHead_counts (x.getD 0 0) (y.getD 0 0) cin (carry.getD 0 0) u v w tail
  simp only [subAffine, List.append_assoc]
  rw [ConstCarry.run_pre _ _ (ConstCarry.notRegister_mc _),
    ConstCarry.run_pre _ _ (ConstCarry.notRegister_mc _), he,
    run_append, run_append (majority _ _ _ _ ++ tail), hct.2]
  congr 1
  apply replaceHead_run _ _ _ _ _ _ _ _ hn hu hv hw
  rw [notRegister_correct y hyn s []]
  simpa only [if_neg hxn, if_pos hy0, if_neg hin, if_neg hun, if_neg hvn, if_neg hwn] using hcarry


theorem subAffine_counts (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length) :
    toffoliCount (subAffine top u v w x y carry cin) + 1 =
      toffoliCount (notRegister y ++ addBase top x y carry cin ++ notRegister y) ∧
    measurementCount (subAffine top u v w x y carry cin) =
      measurementCount (notRegister y ++ addBase top x y carry cin ++ notRegister y) := by
  obtain ⟨tail, he⟩ := addBase_has_head top x y carry cin hx hy hc
  have h := replaceHead_counts (x.getD 0 0) (y.getD 0 0) cin (carry.getD 0 0) u v w tail
  simp only [toffoliCount_append, measurementCount_append] at h
  simp only [subAffine, he, toffoliCount_append, measurementCount_append]
  constructor <;> omega

theorem subAffine_slots (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length) :
    Challenge.gateSlots (subAffine top u v w x y carry cin) ≤
      Challenge.gateSlots (notRegister y ++ addBase top x y carry cin ++ notRegister y) := by
  obtain ⟨tail, he⟩ := addBase_has_head top x y carry cin hx hy hc
  have h := replaceHead_slots (x.getD 0 0) (y.getD 0 0) cin (carry.getD 0 0) u v w tail
  simp only [Challenge.gateSlots_append] at h
  simp only [subAffine, he, Challenge.gateSlots_append]
  omega

theorem subAffine_wires (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length) :
    wires (subAffine top u v w x y carry cin) ⊆
      wires (notRegister y ++ addBase top x y carry cin ++ notRegister y) ∪ {u,v,w} := by
  obtain ⟨tail, he⟩ := addBase_has_head top x y carry cin hx hy hc
  have h := replaceHead_wires (x.getD 0 0) (y.getD 0 0) cin (carry.getD 0 0) u v w tail
  simp only [subAffine, he, wires_append]
  intro q hq
  have hq' := @h q
  simp only [wires_append, Finset.mem_union] at hq hq' ⊢
  tauto

theorem subAffine_physical (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length)
    (hu : u ≠ carry.getD 0 0) (hv : v ≠ carry.getD 0 0) (hw : w ≠ carry.getD 0 0)
    (hp : GatePhysical (notRegister y ++ addBase top x y carry cin ++ notRegister y)) :
    GatePhysical (subAffine top u v w x y carry cin) := by
  obtain ⟨tail, he⟩ := addBase_has_head top x y carry cin hx hy hc
  simp only [subAffine, he, gatePhysical_append] at hp ⊢
  exact ⟨⟨hp.1.1, replaceHead_physical _ _ _ _ _ _ _ _ hu hv hw ((gatePhysical_append _ _).mpr hp.1.2)⟩, hp.2⟩

end ECDSAAdd.Entrant.CodexM6AffineHead


set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.CodexM6AffineHead
open ECDSAAdd ECDSAAdd.Arithmetic

theorem selected_mem (r : List Wire) (i : Nat) (hi : i < r.length) : r.getD i 0 ∈ r := by
  induction r generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem _ (ih _ (by simpa using hi))

theorem selected_count (r : List Wire) (i : Nat) (hi : i < r.length) (q : Wire) :
    [r.getD i 0].count q ≤ r.count q := by
  exact (List.singleton_sublist.mpr (selected_mem r i hi)).count_le q

theorem bit0_value (r : List Wire) (s : BasisState) (h : 0 < r.length) :
    s (r.getD 0 0) = bit0 (regValue r s) := by
  have hv := regValue_bit r 0 0 s h
  cases he : s (r.getD 0 0) <;> simp_all [bit0]

end CodexM6AffineHead

namespace KRegs
open ECDSAAdd ECDSAAdd.Arithmetic CodexM6AffineHead

def m6h (R : KRegs) : Program :=
  subAffine (decide R.trimOK) (R.S.getD 1 0) (R.lo.getD 1 0) (R.hi.getD 1 0)
    (R.dlo ++ R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem m6k_as_base (R : KRegs) : R.m6k =
    notRegister R.T ++ addBase (decide R.trimOK) (R.dlo ++ R.zA) R.T
      (R.carry.take (R.T.length-1)) R.cin ++ notRegister R.T := by
  by_cases ht : R.trimOK <;>
    simp [m6k, addBase, ht, CodexM6Carry.subInPlace2KT, m6c, ConstCarry.subInPlace2]

theorem m6h_counts (R : KRegs) (w : R.W) :
    toffoliCount R.m6h + 1 = toffoliCount R.m6k ∧
    measurementCount R.m6h = measurementCount R.m6k := by
  rw [m6k_as_base]
  have l := R.m6k_lens w
  exact subAffine_counts _ _ _ _ _ _ _ _ (by omega) l.2.2 (by omega)

theorem m6h_slots (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.m6h ≤ Challenge.gateSlots R.m6k := by
  rw [m6k_as_base]
  have l := R.m6k_lens w
  exact subAffine_slots _ _ _ _ _ _ _ _ (by omega) l.2.2 (by omega)

theorem m6h_wires (R : KRegs) (w : R.W) :
    wires R.m6h ⊆ wires R.m6k ∪ {R.S.getD 1 0, R.lo.getD 1 0, R.hi.getD 1 0} := by
  rw [m6k_as_base]
  have l := R.m6k_lens w
  exact subAffine_wires _ _ _ _ _ _ _ _ (by omega) l.2.2 (by omega)

theorem m6h_lengths (R : KRegs) (w : R.W) :
    1 < R.S.length ∧ 1 < R.lo.length ∧ 1 < R.hi.length := by
  have l := R.lens w
  have h4 := w.h4
  have hh := w.hh
  have hS := w.S
  omega

theorem m6h_run (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcarry : carryBit (s.basis ((R.dlo ++ R.zA).getD 0 0))
      (!s.basis (R.T.getD 0 0)) (s.basis R.cin) =
        ((s.basis (R.S.getD 1 0) ^^ s.basis (R.lo.getD 1 0)) ^^ s.basis (R.hi.getD 1 0))) :
    run R.m6h m s = run R.m6k m s := by
  have l := R.m6k_lens w
  have l2 := R.m6h_lengths w
  have mx := selected_mem (R.dlo ++ R.zA) 0 (by omega)
  have my := selected_mem R.T 0 (by omega)
  have mc := selected_mem (R.carry.take (R.T.length-1)) 0 (by omega)
  have mu := selected_mem R.S 1 l2.1
  have mv := selected_mem R.lo 1 l2.2.1
  have mw := selected_mem R.hi 1 l2.2.2
  rw [m6k_as_base]
  apply subAffine_run _ _ _ _ _ _ _ _ (by omega) l.2.2 (by omega)
  · apply knd hn
    intro q
    have c := R.counts q
    have cx := selected_count (R.dlo ++ R.zA) 0 (by omega) q
    have cy := selected_count R.T 0 (by omega) q
    have cc := selected_count (R.carry.take (R.T.length-1)) 0 (by omega) q
    simp only [all, List.count_cons, List.count_append, List.count_nil] at cx cy cc ⊢
    omega
  · exact knd hn (fun q => by simp only [all, List.count_cons, List.count_append]; omega)
  · exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mx
  · have h : R.cin ∈ [R.cin] := by simp
    exact kdis hn (fun q => by simp only [all, List.count_cons, List.count_append, List.count_nil]; omega) _ h
  · exact kdis hn (fun q => by simp only [all, List.count_cons, List.count_append]; omega) _ mu
  · exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mv
  · exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mw
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mu (he ▸ mc)
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mv (he ▸ mc)
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mw (he ▸ mc)
  · exact hcarry


theorem m6h_square_run (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (s : State) (m : List Bool)
    (hclean : ∀ q ∈ R.carry.take (R.T.length - 1), s.basis q = false)
    (hi : s.basis R.cin = false)
    (a b : Nat) (ha : a < 2^R.h) (hb : b < 2^(R.bank.length-R.h))
    (hT : regValue R.T s.basis = (a+b)^2)
    (hA : regValue R.dlo s.basis = a^2)
    (hz : regValue R.zA s.basis = 0)
    (hS : regValue R.S s.basis = a+b)
    (hlo : regValue R.lo s.basis = a)
    (hhi : regValue R.hi s.basis = b) :
    run R.m6h m s = run R.m6 m s := by
  trans run R.m6k m s
  · apply R.m6h_run w hn s m
    have l := R.m6k_lens w
    have la := R.m6c_lens w
    have lc := R.m6h_lengths w
    rw [List.getD_append _ _ _ _ (by omega),
      bit0_value R.dlo s.basis (by omega), bit0_value R.T s.basis (by omega), hA, hT, hi,
      ConstCarry.bit1_value R.S s.basis (by omega),
      ConstCarry.bit1_value R.lo s.basis (by omega),
      ConstCarry.bit1_value R.hi s.basis (by omega), hS, hlo, hhi]
    exact square_head_formula a b
  · apply R.m6k_square_run w _ s m hclean hi a b ha hb hT hA hz
    exact knd hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega)

theorem m6h_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (hp : GatePhysical R.m6) : GatePhysical R.m6h := by
  have l := R.m6k_lens w
  have l2 := R.m6h_lengths w
  have mc := selected_mem (R.carry.take (R.T.length-1)) 0 (by omega)
  have mu := selected_mem R.S 1 l2.1
  have mv := selected_mem R.lo 1 l2.2.1
  have mw := selected_mem R.hi 1 l2.2.2
  have old := R.m6k_physical w hn hp
  rw [m6k_as_base] at old
  apply subAffine_physical _ _ _ _ _ _ _ _ (by omega) l.2.2 (by omega) _ _ _ old
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mu (he ▸ mc)
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mv (he ▸ mc)
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mw (he ▸ mc)

theorem m6h_support (R : KRegs) (w : R.W) (hp : wires R.m6 ⊆ R.all.toFinset) :
    wires R.m6h ⊆ R.all.toFinset := by
  have l := R.m6h_lengths w
  intro q hq
  have h := R.m6h_wires w hq
  rcases Finset.mem_union.mp h with h | h
  · exact hp (R.m6k_wires w h)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · subst q
      have hu := selected_mem R.S 1 l.1
      simp only [all, List.mem_toFinset, List.mem_cons, List.mem_append]
      tauto
    · subst q
      have hv := List.mem_of_mem_take (selected_mem R.lo 1 l.2.1)
      simp only [all, List.mem_toFinset, List.mem_cons, List.mem_append]
      tauto
    · subst q
      have hw := List.mem_of_mem_drop (selected_mem R.hi 1 l.2.2)
      simp only [all, List.mem_toFinset, List.mem_cons, List.mem_append]
      tauto

end KRegs
end ECDSAAdd.Entrant

set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic CodexM6AffineHead

theorem m6h_controls_smk (R : KRegs) (w : R.W) :
    ({R.S.getD 1 0, R.lo.getD 1 0, R.hi.getD 1 0} : Finset Wire) ⊆ wires R.smk := by
  have l := R.lens w
  have lc := R.m6h_lengths w
  have hh := w.hh
  have h4 := w.h4
  have hSl := w.S
  have hcl := w.carry
  have hw4 := addInPlace_wires (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
    (by simp only [List.length_append]; omega)
    (by simp only [List.length_take]; omega)
  have hw3 := copyRegister_wires none R.lo (R.S.take R.h) (by omega)
  have he : R.lo.isEmpty = false := by
    cases hlo : R.lo with
    | nil => simp [hlo] at lc
    | cons a as => rfl
  rw [he] at hw3
  simp only [Bool.false_eq_true, if_false, Option.toList_none, List.nil_append] at hw3
  simp only [smk, wires_append, m3, m4, hw3, hw4]
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with hq | hq | hq
  · subst q
    have hu := selected_mem R.S 1 lc.1
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto
  · subst q
    have hv := selected_mem R.lo 1 lc.2.1
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto
  · subst q
    have hw := selected_mem R.hi 1 lc.2.2
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto

theorem m6h_wires_smk (R : KRegs) (w : R.W) :
    wires R.m6h ⊆ wires R.m6 ∪ wires R.smk :=
  (R.m6h_wires w).trans (Finset.union_subset_union (R.m6k_wires w) (R.m6h_controls_smk w))

end ECDSAAdd.Entrant.KRegs

end

-- First c6 carry is already present in target bit1.
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.CodexC6Head
open ECDSAAdd ECDSAAdd.Arithmetic

def add3h : List Wire → List Wire → List Wire → Wire → Program
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, cin =>
      [.CX b1 c0] ++ ([.CX b1 c1] ++ addInPlace (a2 :: as) (b2 :: bs) cs c1 ++
        eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++
        eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0]
  | x, y, c, cin => ConstCarry.addInPlace3 x y c cin

theorem head_eq (a b cin c u : Wire) (hn : [a,b,cin,c].Nodup)
    (s : State) (m : List Bool)
    (hb : s.basis u = carryBit (s.basis a) (s.basis b) (s.basis cin)) :
    run [.CX u c] m s = run (majority a b cin c) m s := by
  rw [majority_correct a b cin c hn s m]
  simp only [run, hb]

theorem run_shape (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire)
    (hn : [a0,b0,cin,c0].Nodup) (s : State) (m : List Bool)
    (hb : s.basis b1 = carryBit (s.basis a0) (s.basis b0) (s.basis cin)) :
    run (add3h (a0::a1::a2::as) (b0::b1::b2::bs) (c0::c1::cs) cin) m s =
      run (ConstCarry.addInPlace3 (a0::a1::a2::as) (b0::b1::b2::bs) (c0::c1::cs) cin) m s := by
  simp only [add3h, ConstCarry.addInPlace3, List.append_assoc]
  rw [ConstCarry.run_pre _ _ (by simp [measurementCount]),
    ConstCarry.run_pre _ _ (ConstCarry.majority_mc _ _ _ _),
    head_eq _ _ _ _ _ hn s [] hb]

theorem run_eq (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x++y++carry)).Nodup)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length)
    (s : State) (m : List Bool)
    (hb : s.basis (y.getD 1 0) = carryBit (s.basis (x.getD 0 0))
      (s.basis (y.getD 0 0)) (s.basis cin)) :
    run (add3h x y carry cin) m s = run (ConstCarry.addInPlace3 x y carry cin) m s := by
  match x,y,carry,hx,hy,hc with
  | a0::a1::a2::as, b0::b1::b2::bs, c0::c1::cs, _,_,_ =>
    simp only [List.getD_cons_succ,List.getD_cons_zero] at hb
    apply run_shape _ _ _ _ _ _ _ _ _ _ _ _ _ s m hb
    exact knd hn (fun q => by simp only [List.count_cons,List.count_nil,List.count_append]; omega)

theorem resources (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    toffoliCount (add3h x y carry cin)+1 = toffoliCount (ConstCarry.addInPlace3 x y carry cin) ∧
    measurementCount (add3h x y carry cin) = measurementCount (ConstCarry.addInPlace3 x y carry cin) ∧
    wires (add3h x y carry cin) ⊆ wires (ConstCarry.addInPlace3 x y carry cin) ∧
    Challenge.gateSlots (add3h x y carry cin) ≤ Challenge.gateSlots (ConstCarry.addInPlace3 x y carry cin) := by
  match x,y,carry,hx,hy,hc with
  | a0::a1::a2::as, b0::b1::b2::bs, c0::c1::cs, _,_,_ =>
    refine ⟨?_,?_,?_,?_⟩
    · simp [add3h,ConstCarry.addInPlace3,majority,toffoliCount,Nat.add_comm]
    · simp [add3h,ConstCarry.addInPlace3,majority,measurementCount]
    · simp only [add3h,ConstCarry.addInPlace3,wires_append]
      intro q hq
      simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at hq
      simp only [majority,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty]
      tauto
    · simp only [add3h,ConstCarry.addInPlace3,Challenge.gateSlots_append]
      simp [majority,Challenge.gateSlots,Challenge.instructionSlots]

theorem physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x++y++carry)).Nodup)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length)
    (hp : GatePhysical (ConstCarry.addInPlace3 x y carry cin)) :
    GatePhysical (add3h x y carry cin) := by
  match x,y,carry,hx,hy,hc with
  | a0::a1::a2::as, b0::b1::b2::bs, c0::c1::cs, _,_,_ =>
    have hbc : b1 ≠ c0 := by
      intro he
      have hd := kdis (r := [b1]) (t := [c0]) hn (fun q => by
        simp only [List.count_cons,List.count_nil,List.count_append]; omega) b1 (by simp)
      exact hd (by simpa using he)
    have hp' : GatePhysical [.CX b1 c0] := by
      simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hbc]
    simp only [add3h,ConstCarry.addInPlace3,gatePhysical_append] at hp ⊢
    tauto


end ECDSAAdd.Entrant.CodexC6Head

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic

def c6h (R : KRegs) : Program :=
  CodexC6Head.add3h (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem c6h_counts (R : KRegs) (w : R.W) :
    toffoliCount R.c6h + 1 = toffoliCount R.c6c ∧
    measurementCount R.c6h = measurementCount R.c6c := by
  have l := R.m6c_lens w
  have h := CodexC6Head.resources (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin l.1 l.2.1 l.2.2.1
  exact ⟨h.1,h.2.1⟩

theorem c6h_wires (R : KRegs) (w : R.W) : wires R.c6h ⊆ wires R.c6 := by
  have l := R.m6c_lens w
  have h := CodexC6Head.resources (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin l.1 l.2.1 l.2.2.1
  exact h.2.2.1.trans (R.c6c_wires w)

theorem c6h_slots (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.c6h ≤ Challenge.gateSlots R.c6 := by
  have l := R.m6c_lens w
  have h := CodexC6Head.resources (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin l.1 l.2.1 l.2.2.1
  exact h.2.2.2.trans (R.c6c_slots w)

theorem c6h_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (hp : GatePhysical R.c6) : GatePhysical R.c6h := by
  have l := R.m6c_lens w
  apply CodexC6Head.physical _ _ _ _ _ l.1 l.2.1 l.2.2.1 (R.c6c_physical w hp)
  exact knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega)

theorem c6h_run (R : KRegs) (w : R.W)
    (hn : (R.cin::((R.dlo++R.zA)++R.T++R.carry.take (R.T.length-1))).Nodup)
    (s : State) (m : List Bool) (hc0 : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hi : s.basis R.cin=false)
    (hb : s.basis (R.T.getD 1 0)=(s.basis (R.dlo.getD 0 0) && s.basis (R.T.getD 0 0))) :
    run R.c6h m s = run R.c6 m s := by
  trans run R.c6c m s
  · have l := R.m6c_lens w
    apply CodexC6Head.run_eq _ _ _ _ hn l.1 l.2.1 l.2.2.1
    rw [hb,List.getD_append _ _ _ _ (by omega),hi]
    cases s.basis (R.dlo.getD 0 0) <;> cases s.basis (R.T.getD 0 0) <;> rfl
  · exact R.c6c_run w hn s m hc0 hi hb

end ECDSAAdd.Entrant.KRegs

end

namespace ECDSAAdd.Entrant.LowZero18KG
open Arithmetic KG
variable (K : KG)
def make : Program := K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591
def clear : Program := K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c
theorem make_correct (sp : K.Spec) (hn : K.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=0) (hS0 : regValue K.R.S s.basis=0)
    (hT0 : regValue K.R.T s.basis=0) (hX0 : regValue K.X s.basis=0)
    (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    (run (make K) m s).phase=s.phase ∧
    regValue K.R.dst (run (make K) m s).basis=(regValue K.R.bank s.basis)^2 ∧
    regValue K.R.S (run (make K) m s).basis=0 ∧
    regValue K.R.T (run (make K) m s).basis=2*regValue K.R.lo s.basis*regValue K.R.hi s.basis ∧
    K.I1 (regValue K.R.lo s.basis) (run (make K) m s).basis ∧
    K.I2 (regValue K.R.hi s.basis) (run (make K) m s).basis ∧
    K.I5 (regValue K.R.lo s.basis+regValue K.R.hi s.basis) (run (make K) m s).basis ∧
    ∀q,q∉K.R.dst → q∉K.R.T → q∉K.X → (run (make K) m s).basis q=s.basis q := by
  have w := sp.w
  have hR := K.rnd hn
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := K.R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have bv := K.R.bank_value w s.basis
  rw [bv]
  generalize ha : regValue K.R.lo s.basis=a
  generalize hb : regValue K.R.hi s.basis=b
  have aLt : a<2^K.R.h := by rw [←ha,←L0]; exact regValue_lt _ _
  have bLt : b<2^(K.R.bank.length-K.R.h) := by rw [←hb,←L1]; exact regValue_lt _ _
  have mt {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.take k) : q∈l := List.mem_of_mem_take h
  have md {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.drop k) : q∈l := List.mem_of_mem_drop h
  have x1 {q : Wire} (h : q∈K.X1) : q∈K.X := by simp [X,h]
  have x2 {q : Wire} (h : q∈K.X2) : q∈K.X := by simp [X,h]
  have x5 {q : Wire} (h : q∈K.X5) : q∈K.X := by simp [X,h]
  have xo (q : Wire) (h : q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) : q∉K.X := by
    apply K.rX hn q; simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
  have outV (t : State) (G : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t.basis q=s.basis q) (r : List Wire)
      (hr : ∀q∈r,q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) :
      regValue r t.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => let o := K.R.outside hR q (hr q hq); G q o.1 o.2.1 o.2.2 (xo q (hr q hq)))
  have zero (r : List Wire) (big : List Wire) (hz : regValue big s.basis=0) (sub : ∀q∈r,q∈big) :
      regValue r s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (sub q hq))
  have nD : K.R.dst.Nodup := knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have cinO : K.R.cin∉K.R.dst ∧ K.R.cin∉K.R.S ∧ K.R.cin∉K.R.T := K.R.outside hR K.R.cin (by simp)
  have cinX : K.R.cin∉K.X := xo _ (by simp)
  obtain ⟨a7,r8,e8⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z) K.R.scl1591 m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k) K.R.m8z a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6h) K.R.m7k a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5) K.R.m6h a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.Q1++K.Q2++K.R.smk) K.Q5 a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.Q1++K.Q2) K.R.smk a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.Q1 K.Q2 a2 s
  rw [show (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591 from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- Q1: a^2 into dlo
  have st1 := sp.mk1 s r1 (zero _ _ hd0 (fun q h => mt h)) (zero _ _ hX0 (fun q h => x1 h)) hp0 hc0 hz0 hi0
  rw [ha] at st1
  generalize run K.Q1 r1 s=s1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s1.basis q=s.basis q :=
    fun q h _ _ x => st1.2.2.2 q (fun y => h (mt y)) (fun y => x (x1 y))
  -- Q2: b^2 into dhi
  have dhi1 : regValue K.R.dhi s1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hd0 (fun q h => md h))
  have X21 : regValue K.X2 s1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hX0 (fun q h => x2 h))
  have hi1 : regValue K.R.hi s1.basis=b := (outV s1 G1 _ (fun q h => Or.inl (md h))).trans hb
  have st2 := sp.mk2 s1 r2 dhi1 X21 ((outV s1 G1 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV s1 G1 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV s1 G1 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  rw [hi1] at st2
  generalize run K.Q2 r2 s1=s2 at st2 ⊢
  have F2 : ∀q,q∉K.R.dhi → q∉K.X2 → s2.basis q=s1.basis q := st2.2.2.2
  have G2 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s2.basis q=s.basis q :=
    fun q h hS hT x => (F2 q (fun y => h (md y)) (fun y => x (x2 y))).trans (G1 q h hS hT x)
  have dlo2 : regValue K.R.dlo s2.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st1.2.1
  have I12 : K.I1 a s2.basis := sp.lc1 a s1.basis s2.basis (fun q hq => (F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st1.2.2.1
  -- sum register
  have S2 : regValue K.R.S s2.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    (F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).trans (st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)))).trans hS0
  have st3 := K.R.smk_correct w hR s2 r3 S2 ((outV s2 G2 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s2 G2 K.R.carry (by intro q h; simp [h])).trans hc0) ((G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  have lo2 : regValue K.R.lo s2.basis=a := (outV s2 G2 K.R.lo (fun q h => Or.inl (mt h))).trans ha
  have hi2 : regValue K.R.hi s2.basis=b := (outV s2 G2 K.R.hi (fun q h => Or.inl (md h))).trans hb
  rw [lo2,hi2] at st3
  generalize run K.R.smk r3 s2=s3 at st3 ⊢
  have F3 := st3.2.2
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s3.basis q=s.basis q :=
    fun q h hS hT x => (F3 q hS).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo s3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi s3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st2.2.1
  have I13 : K.I1 a s3.basis := sp.lc1 a s2.basis s3.basis (fun q hq => (F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I12
  have I23 : K.I2 b s3.basis := sp.lc2 b s2.basis s3.basis (fun q hq => (F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st2.2.2.1
  -- Q5: T = (a+b)^2
  have back3 (q : Wire) (h1 : q∉K.R.dlo) (h2 : q∉K.X1) (h3 : q∉K.R.dhi) (h4 : q∉K.X2) (h5 : q∉K.R.S) :
      s3.basis q=s.basis q :=
    (F3 q h5).trans ((F2 q h3 h4).trans (st1.2.2.2 q h1 h2))
  have T3 : regValue K.R.T s3.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    back3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have X53 : regValue K.X5 s3.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    back3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hX0 (fun q h => x5 h))
  have st5 := sp.mk5 s3 r4 T3 X53 ((outV s3 G3 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV s3 G3 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV s3 G3 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  rw [st3.2.1] at st5
  generalize run K.Q5 r4 s3=s5 at st5 ⊢
  have F5 : ∀q,q∉K.R.T → q∉K.X5 → s5.basis q=s3.basis q := st5.2.2.2
  have G5 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s5.basis q=s.basis q :=
    fun q h hS hT x => (F5 q hT (fun y => x (x5 y))).trans (G3 q h hS hT x)
  have dlo5 : regValue K.R.dlo s5.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo3
  have dhi5 : regValue K.R.dhi s5.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi3
  have S5 : regValue K.R.S s5.basis=a+b := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st3.2.1
  have I15 : K.I1 a s5.basis := sp.lc1 a s3.basis s5.basis (fun q hq => (F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I13
  have I25 : K.I2 b s5.basis := sp.lc2 b s3.basis s5.basis (fun q hq => (F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I23
  have sumLt : a+b<2^K.R.S.length := by
    have hp : 2^K.R.h≤2^(K.R.bank.length-K.R.h) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : 2^K.R.S.length=2*2^(K.R.bank.length-K.R.h) := by rw [hSl,pow_succ]; ring
    omega
  have sqLt : (a+b)^2<2^K.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  -- T -= a^2
  have st6 : (run K.R.m6h r5 s5).phase=s5.phase ∧ regValue K.R.T (run K.R.m6h r5 s5).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run K.R.m6h r5 s5).basis q=s5.basis q := by
    rw [K.R.m6h_square_run w hR
      s5 r5
      (fun q hq => (regValue_zero _ _).mp ((outV s5 G5 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      ((G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
      a b aLt bLt st5.2.1 dlo5
      ((outV s5 G5 K.R.zA (by intro q h; simp [mt h])).trans
        (zero K.R.zA K.R.z hz0 (fun q h =>
          List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h))))
      S5
      ((outV s5 G5 K.R.lo (fun q h => Or.inl (mt h))).trans ha)
      ((outV s5 G5 K.R.hi (fun q h => Or.inl (md h))).trans hb)]
    unfold KRegs.m6
    obtain ⟨p,f,v⟩ := BalancedInverse.subInPlace_any_correct (K.R.dlo++K.R.zA) K.R.T
      (K.R.carry.take (K.R.T.length-1)) K.R.cin (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega)
      (by simp only [List.length_take]; omega) s5 r5
      (fun q hq => (regValue_zero _ _).mp ((outV s5 G5 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dlo5,outV s5 G5 K.R.zA (by intro q h; simp [mt h]),zero K.R.zA K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h)),
      st5.2.1,G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [ex]; omega) sqLt,ex]; omega
  generalize run K.R.m6h r5 s5=s6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hT).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo s6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi s6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  -- T -= b^2
  have xv6 : regValue (K.R.dhi++K.R.zB) s6.basis=b^2 := by
    rw [regValue_append,dhi6,outV s6 G6 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h))]; simp
  have st7 : (run K.R.m7k r6 s6).phase=s6.phase ∧ regValue K.R.T (run K.R.m7k r6 s6).basis=2*a*b ∧
      ∀q,q∉K.R.T → (run K.R.m7k r6 s6).basis q=s6.basis q := by
    have hcl7 : ∀q∈K.R.carry.take (K.R.T.length-1),s6.basis q=false :=
      (fun q hq => (regValue_zero _ _).mp ((outV s6 G6 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    have hnc7 : (s6.basis ((K.R.dhi++K.R.zB).headD 0) && !s6.basis (K.R.T.headD 0))=false :=
      (by
        have hT := LowZero.head_bit K.R.T [] s6.basis (K.R.T_ne w)
        rw [List.append_nil] at hT
        rw [LowZero.head_bit K.R.dhi K.R.zB s6.basis (K.R.dhi_ne w),hT,dhi6,st6.2.1,
          show 2*a*b+b^2=b^2+2*(a*b) by ring,Nat.add_mul_mod_self_left]
        cases decide (b^2%2=1) <;> rfl)
    have hi7 : s6.basis K.R.cin=false :=
      ((G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    have h17 : s6.basis ((K.R.dhi++K.R.zB).tail.headD 0)=false :=
      (by rw [ECDSAAdd.Entrant.KRegs.bit1 K.R.dhi K.R.zB s6.basis (K.R.dhi_two w),dhi6,ECDSAAdd.Entrant.KRegs.sq_bit1]; rfl)
    have hA7 : K.R.trimOK → regValue (K.R.dhi++K.R.zB) s6.basis<2^(K.R.T.length-1) :=
      (fun _ => by rw [xv6,hTl,hSl]; exact ECDSAAdd.Entrant.KRegs.sq_trim_bound K.R.bank.length K.R.h b bLt)
    have hb7 : K.R.trimOK → regValue (K.R.dhi++K.R.zB) s6.basis≤regValue K.R.T s6.basis%2^(K.R.T.length-1) :=
      (fun tc => by
        have tb := ECDSAAdd.Entrant.KRegs.trim_bound K.R.bank.length K.R.h a b tc aLt bLt
        rw [xv6,st6.2.1,hTl,hSl,Nat.mod_eq_of_lt tb]; omega)
    have hab7 : a*b<2^K.R.bank.length := by
      have e : 2^K.R.bank.length=2^K.R.h*2^(K.R.bank.length-K.R.h) := by rw [←pow_add]; congr 1; omega
      rw [e]; exact Nat.mul_lt_mul'' aLt bLt
    have p2b : 2^(K.R.bank.length+1)=2*2^K.R.bank.length := by rw [pow_succ]; ring
    have HT : K.R.trimOK → regValue (K.R.dhi++K.R.zB) s6.basis<2^(K.R.T.length-1) ∧
        regValue (K.R.dhi++K.R.zB) s6.basis≤regValue K.R.T s6.basis%2^(K.R.T.length-1) ∧
        regValue K.R.T s6.basis%2^(K.R.T.length-1)<regValue (K.R.dhi++K.R.zB) s6.basis+2^(K.R.T.length-2) := by
      intro tc
      refine ⟨hA7 tc,hb7 tc,?_⟩
      have tc' : 2*K.R.h+1≤K.R.bank.length := tc
      have tb := ECDSAAdd.Entrant.KRegs.trim_bound K.R.bank.length K.R.h a b tc aLt bLt
      have hpw : 2^(K.R.bank.length+1)≤2^(K.R.T.length-2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [xv6,st6.2.1,hTl,hSl,Nat.mod_eq_of_lt tb]
      rw [hTl,hSl] at hpw
      rw [show 2*a*b+b^2=2*(a*b)+b^2 by ring]; omega
    have HF : ¬K.R.trimOK → regValue (K.R.dhi++K.R.zB) s6.basis≤regValue K.R.T s6.basis ∧
        regValue K.R.T s6.basis<regValue (K.R.dhi++K.R.zB) s6.basis+2^(K.R.T.length-1) := by
      intro _
      have hpw : 2^(K.R.bank.length+1)≤2^(K.R.T.length-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [xv6,st6.2.1,show 2*a*b+b^2=2*(a*b)+b^2 by ring]
      constructor <;> omega
    rw [K.R.m7k_run w hR s6 r6 hcl7 hnc7 hi7 h17 HT HF]
    obtain ⟨p,f,v⟩ := K.R.m7t_correct w hR s6 r6 hcl7 hnc7 hi7 h17 hA7 hb7
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi6,outV s6 G6 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      st6.2.1,G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by omega) (by rw [ex] at sqLt; omega)]; omega
  generalize run K.R.m7k r6 s6=s7 at st7 ⊢
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s7.basis q=s.basis q :=
    fun q h hS hT x => (st7.2.2 q hT).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo s7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  have dhi7 : regValue K.R.dhi s7.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi6
  have D7 : regValue K.R.dst s7.basis=a^2+2^(2*K.R.h)*b^2 := by rw [K.R.dst_value w,dlo7,dhi7]
  -- dst += 2^h * 2ab
  have st8 : (run K.R.m8z r7 s7).phase=s7.phase ∧
      regValue K.R.dmid (run K.R.m8z r7 s7).basis=(2*a*b+(a^2+2^(2*K.R.h)*b^2)/2^K.R.h)%2^(2*K.R.bank.length-K.R.h) ∧
      ∀q,q∉K.R.dmid → (run K.R.m8z r7 s7).basis q=s7.basis q := by
    obtain ⟨p,f,v⟩ := K.R.m8z_correct w hR s7 r7 (a*b)
      (fun q hq => (regValue_zero _ _).mp ((outV s7 G7 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by rw [st7.2.1]; ring) ((G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,st7.2.1,outV s7 G7 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      show regValue K.R.dmid s7.basis=regValue K.R.dst s7.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) s7.basis,D7,
      G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,L4]
    simp
  generalize run K.R.m8z r7 s7=s8 at st8 ⊢
  have G8 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s8.basis q=s.basis q :=
    fun q h hS hT x => (st8.2.2 q (fun y => h (md y))).trans (G7 q h hS hT x)
  have D8 : regValue K.R.dst s8.basis=(a+2^K.R.h*b)^2 := by
    rw [K.R.dst_value_mid w,st8.2.1,kkeep st8.2.2 (by
      intro q hq hx
      have c1 := List.count_pos_iff.mpr hq; have c2 := List.count_pos_iff.mpr hx
      have c3 := (K.R.counts q).2.2.1
      have c4 := List.nodup_iff_count_le_one.mp nD q
      omega),CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst K.R.h (by omega),D7]
    exact KRegs.kfinal a b K.R.h K.R.bank.length aLt bLt (by omega)
  -- facts between s5 and s8: only T and dmid changed
  have back8 (q : Wire) (hT : q∉K.R.T) (hd : q∉K.R.dst) : s8.basis q=s5.basis q :=
    (st8.2.2 q (fun y => hd (md y))).trans ((st7.2.2 q hT).trans (st6.2.2 q hT))
  have S8 : regValue K.R.S s8.basis=a+b := (regValue_congr _ _ _ (fun q hq => back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S5
  have T8 : regValue K.R.T s8.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st8.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.1
  have I18 : K.I1 a s8.basis := sp.lc1 a s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I15
  have I28 : K.I2 b s8.basis := sp.lc2 b s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I25
  have I58 : K.I5 (a+b) s8.basis := sp.lc5 (a+b) s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st5.2.2.1
  -- clean the sum register
  have st9 := K.R.scl1591_correct w hR s8 r8
    (by rw [S8,(outV s8 G8 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV s8 G8 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV s8 G8 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s8 G8 K.R.carry (by intro q h; simp [h])).trans hc0) ((G8 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl1591 r8 s8=s9 at st9 ⊢
  refine ⟨st9.1.trans (st8.1.trans (st7.1.trans (st6.1.trans (st5.1.trans (st3.1.trans
    (st2.1.trans st1.1)))))),?_,st9.2.1,?_,?_,?_,?_,?_⟩
  · rw [←D8]; exact regValue_congr _ _ _ (fun q hq => st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))
  · rw [←T8]; exact regValue_congr _ _ _ (fun q hq => st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))
  · exact sp.lc1 a s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I18
  · exact sp.lc2 b s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I28
  · exact sp.lc5 (a+b) s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I58
  · intro q hd hT hx
    by_cases hS : q∈K.R.S
    · exact ((regValue_zero _ _).mp st9.2.1 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
    · exact (st9.2.2 q hS).trans (G8 q hd hS hT hx)

theorem clear_correct (sp : K.Spec) (hn : K.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=(regValue K.R.bank s.basis)^2) (hS0 : regValue K.R.S s.basis=0)
    (hT0 : regValue K.R.T s.basis=2*regValue K.R.lo s.basis*regValue K.R.hi s.basis)
    (hI1 : K.I1 (regValue K.R.lo s.basis) s.basis) (hI2 : K.I2 (regValue K.R.hi s.basis) s.basis)
    (hI5 : K.I5 (regValue K.R.lo s.basis+regValue K.R.hi s.basis) s.basis)
    (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    (run (clear K) m s).phase=s.phase ∧
    regValue K.R.dst (run (clear K) m s).basis=0 ∧
    regValue K.R.S (run (clear K) m s).basis=0 ∧
    regValue K.R.T (run (clear K) m s).basis=0 ∧
    regValue K.X (run (clear K) m s).basis=0 ∧
    ∀q,q∉K.R.dst → q∉K.R.T → q∉K.X → (run (clear K) m s).basis q=s.basis q := by
  have w := sp.w
  have hR := K.rnd hn
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := K.R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  rw [K.R.bank_value w s.basis] at hd0
  generalize ha : regValue K.R.lo s.basis=a at hd0 hT0 hI1 hI5
  generalize hb : regValue K.R.hi s.basis=b at hd0 hT0 hI2 hI5
  have aLt : a<2^K.R.h := by rw [←ha,←L0]; exact regValue_lt _ _
  have bLt : b<2^(K.R.bank.length-K.R.h) := by rw [←hb,←L1]; exact regValue_lt _ _
  have mt {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.take k) : q∈l := List.mem_of_mem_take h
  have md {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.drop k) : q∈l := List.mem_of_mem_drop h
  have x1 {q : Wire} (h : q∈K.X1) : q∈K.X := by simp [X,h]
  have x2 {q : Wire} (h : q∈K.X2) : q∈K.X := by simp [X,h]
  have x5 {q : Wire} (h : q∈K.X5) : q∈K.X := by simp [X,h]
  have xo (q : Wire) (h : q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) : q∉K.X := by
    apply K.rX hn q; simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
  have outV (t : State) (G : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t.basis q=s.basis q) (r : List Wire)
      (hr : ∀q∈r,q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) :
      regValue r t.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => let o := K.R.outside hR q (hr q hq); G q o.1 o.2.1 o.2.2 (xo q (hr q hq)))
  have zero (r : List Wire) (big : List Wire) (hz : regValue big s.basis=0) (sub : ∀q∈r,q∈big) :
      regValue r s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (sub q hq))
  have nD : K.R.dst.Nodup := knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have cinO : K.R.cin∉K.R.dst ∧ K.R.cin∉K.R.S ∧ K.R.cin∉K.R.T := K.R.outside hR K.R.cin (by simp)
  have cinX : K.R.cin∉K.X := xo _ (by simp)
  have hp2 : 2^K.R.h≤2^(K.R.bank.length-K.R.h) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq2 : 2^K.R.S.length=2*2^(K.R.bank.length-K.R.h) := by rw [hSl,pow_succ]; ring
  have sumLt : a+b<2^K.R.S.length := by omega
  have sqLt : (a+b)^2<2^K.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  have hX : (a+2^K.R.h*b)^2=(a^2+2^(2*K.R.h)*b^2)+2^K.R.h*(2*a*b) := by ring
  have hpos : 0<2^K.R.h := Nat.two_pow_pos _
  have XLt : (a+2^K.R.h*b)^2<2^(2*K.R.bank.length) := by
    have hsplit : 2^K.R.bank.length=2^K.R.h*2^(K.R.bank.length-K.R.h) := by rw [←pow_add]; congr 1; omega
    have hm := Nat.mul_le_mul_left (2^K.R.h) (show b+1≤2^(K.R.bank.length-K.R.h) by omega)
    rw [Nat.mul_add,Nat.mul_one,←hsplit] at hm
    exact square_bound _ _ (by omega)
  have aSq : a^2<2^(2*K.R.h) := square_bound _ _ aLt
  obtain ⟨a7,r8,e8⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591++K.Q2c) K.Q1c m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591) K.Q2c a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c) K.R.scl1591 a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h) K.Q5c a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7t) K.R.c6h a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.R.smk++K.R.c8z) K.R.c7t a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.R.smk K.R.c8z a2 s
  rw [show (clear K)=K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- rebuild S
  have st1 := K.R.smk_correct w hR s r1 hS0 hz0 hc0 hi0
  rw [ha,hb] at st1
  generalize run K.R.smk r1 s=t1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t1.basis q=s.basis q := fun q _ h _ _ => st1.2.2 q h
  have T1 : regValue K.R.T t1.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have D1 : regValue K.R.dst t1.basis=(a+2^K.R.h*b)^2 := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hd0
  -- dst -= 2^h * 2ab
  have st2 : (run K.R.c8z r2 t1).phase=t1.phase ∧
      regValue K.R.dst (run K.R.c8z r2 t1).basis=a^2+2^(2*K.R.h)*b^2 ∧
      ∀q,q∉K.R.dmid → (run K.R.c8z r2 t1).basis q=t1.basis q := by
    obtain ⟨p,f,v⟩ := K.R.c8z_correct w hR t1 r2
      (fun q hq => (regValue_zero _ _).mp ((outV t1 G1 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by rw [LowZero.head_false_of_even K.R.T K.R.zM t1.basis (a*b) (by rw [T1]; ring) (K.R.T_ne w)]; rfl)
      ((G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    refine ⟨p,?_,f⟩
    rw [K.R.dst_value_mid w,v,kkeep f (by
      intro q hq hx
      have c1 := List.count_pos_iff.mpr hq; have c2 := List.count_pos_iff.mpr hx
      have c3 := (K.R.counts q).2.2.1
      have c4 := List.nodup_iff_count_le_one.mp nD q
      omega),regValue_append,T1,outV t1 G1 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst K.R.h (by omega),
      show regValue K.R.dmid t1.basis=regValue K.R.dst t1.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) t1.basis,D1,L4]
    have hdiv : (a+2^K.R.h*b)^2/2^K.R.h=(a^2+2^(2*K.R.h)*b^2)/2^K.R.h+2*a*b := by
      rw [hX,Nat.add_mul_div_left _ _ hpos]
    have hmod : (a+2^K.R.h*b)^2%2^K.R.h=(a^2+2^(2*K.R.h)*b^2)%2^K.R.h := by
      rw [hX,Nat.add_mul_mod_self_left]
    have hq : (a+2^K.R.h*b)^2/2^K.R.h<2^(2*K.R.bank.length-K.R.h) := by
      rw [Nat.div_lt_iff_lt_mul hpos,←pow_add,show 2*K.R.bank.length-K.R.h+K.R.h=2*K.R.bank.length by omega]
      exact XLt
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod ((a+2^K.R.h*b)^2/2^K.R.h) (2*a*b) _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  generalize run K.R.c8z r2 t1=t2 at st2 ⊢
  have G2 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t2.basis q=s.basis q :=
    fun q h hS hT x => (st2.2.2 q (fun y => h (md y))).trans (G1 q h hS hT x)
  have dlo2 : regValue K.R.dlo t2.basis=a^2 := by
    rw [show regValue K.R.dlo t2.basis=regValue K.R.dst t2.basis%2^(2*K.R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst (2*K.R.h) (by omega) t2.basis,st2.2.1,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt aSq]
  have dhi2 : regValue K.R.dhi t2.basis=b^2 := by
    rw [show regValue K.R.dhi t2.basis=regValue K.R.dst t2.basis/2^(2*K.R.h) from
      CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst (2*K.R.h) (by omega) t2.basis,st2.2.1,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt aSq,Nat.zero_add]
  have S2 : regValue K.R.S t2.basis=a+b := (regValue_congr _ _ _ (fun q hq => st2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st1.2.1
  have T2 : regValue K.R.T t2.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans T1
  -- T += b^2
  have xv2 : regValue (K.R.dhi++K.R.zB) t2.basis=b^2 := by
    rw [regValue_append,dhi2,outV t2 G2 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h))]; simp
  have st3 : (run K.R.c7t r3 t2).phase=t2.phase ∧ regValue K.R.T (run K.R.c7t r3 t2).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run K.R.c7t r3 t2).basis q=t2.basis q := by
    obtain ⟨p,f,v⟩ := K.R.c7t_correct w hR t2 r3
      (fun q hq => (regValue_zero _ _).mp ((outV t2 G2 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by
        have hT := LowZero.head_false_of_even K.R.T [] t2.basis (a*b) (by rw [T2]; ring) (K.R.T_ne w)
        rw [List.append_nil] at hT
        rw [hT]; exact Bool.and_false _)
      ((G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
      (by rw [ECDSAAdd.Entrant.KRegs.bit1 K.R.dhi K.R.zB t2.basis (K.R.dhi_two w),dhi2,ECDSAAdd.Entrant.KRegs.sq_bit1]; rfl)
      (fun _ => by rw [xv2,hTl,hSl]; exact ECDSAAdd.Entrant.KRegs.sq_trim_bound K.R.bank.length K.R.h b bLt)
      (fun tc => by
        have tb := ECDSAAdd.Entrant.KRegs.trim_bound K.R.bank.length K.R.h a b tc aLt bLt
        rw [xv2,T2,hTl,hSl,Nat.mod_eq_of_lt (by omega)]; omega)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi2,outV t2 G2 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      T2,G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega)]; ring
  generalize run K.R.c7t r3 t2=t3 at st3 ⊢
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t3.basis q=s.basis q :=
    fun q h hS hT x => (st3.2.2 q hT).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo t3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi t3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi2
  have S3 : regValue K.R.S t3.basis=a+b := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S2
  -- T += a^2
  have st4 : (run K.R.c6h r4 t3).phase=t3.phase ∧ regValue K.R.T (run K.R.c6h r4 t3).basis=(a+b)^2 ∧
      ∀q,q∉K.R.T → (run K.R.c6h r4 t3).basis q=t3.basis q := by
    rw [K.R.c6h_run w (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega))
      t3 r4 (fun q hq => (regValue_zero _ _).mp ((outV t3 G3 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq) ((G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
      (K.R.c6c_bits w t3.basis a b st3.2.1 dlo3)]
    unfold KRegs.c6
    obtain ⟨p,f,v⟩ := addInPlace_correct (K.R.dlo++K.R.zA) K.R.T (K.R.carry.take (K.R.T.length-1)) K.R.cin
      (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t3 r4
      (fun q hq => (regValue_zero _ _).mp ((outV t3 G3 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dlo3,outV t3 G3 K.R.zA (by intro q h; simp [mt h]),zero K.R.zA K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h)),
      st3.2.1,G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega),ex]; ring
  generalize run K.R.c6h r4 t3=t4 at st4 ⊢
  have G4 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t4.basis q=s.basis q :=
    fun q h hS hT x => (st4.2.2 q hT).trans (G3 q h hS hT x)
  have dlo4 : regValue K.R.dlo t4.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo3
  have dhi4 : regValue K.R.dhi t4.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi3
  have S4 : regValue K.R.S t4.basis=a+b := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S3
  have back4 (q : Wire) (h1 : q∉K.R.S) (h2 : q∉K.R.dst) (h3 : q∉K.R.T) : t4.basis q=s.basis q :=
    (st4.2.2 q h3).trans ((st3.2.2 q h3).trans ((st2.2.2 q (fun y => h2 (md y))).trans (st1.2.2 q h1)))
  -- clear T with the S-square cleanup
  have st5 := sp.cl5 t4 r5 (by rw [st4.2.1,S4])
    (by rw [S4]; exact sp.lc5 (a+b) s.basis t4.basis (fun q hq => (back4 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) hI5)
    ((outV t4 G4 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t4 G4 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t4 G4 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G4 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q5c r5 t4=t5 at st5 ⊢
  have F5 : ∀q,q∉K.R.T → q∉K.X5 → t5.basis q=t4.basis q := st5.2.2.2
  have G5 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t5.basis q=s.basis q :=
    fun q h hS hT x => (F5 q hT (fun y => x (x5 y))).trans (G4 q h hS hT x)
  have dlo5 : regValue K.R.dlo t5.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo4
  have dhi5 : regValue K.R.dhi t5.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi4
  have S5 : regValue K.R.S t5.basis=a+b := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S4
  -- clean S
  have st6 := K.R.scl1591_correct w hR t5 r6
    (by rw [S5,(outV t5 G5 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV t5 G5 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV t5 G5 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV t5 G5 K.R.carry (by intro q h; simp [h])).trans hc0) ((G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl1591 r6 t5=t6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hS).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo t6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi t6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  have T6 : regValue K.R.T t6.basis=0 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st5.2.1
  have X56 : regValue K.X5 t6.basis=0 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st5.2.2.1
  have back6 (q : Wire) (h1 : q∉K.R.S) (h2 : q∉K.R.dst) (h3 : q∉K.R.T) (h4 : q∉K.X5) : t6.basis q=s.basis q :=
    (st6.2.2 q h1).trans ((F5 q h3 h4).trans (back4 q h1 h2 h3))
  -- clear b^2
  have st7 := sp.cl2 t6 r7
    (by rw [dhi6,(outV t6 G6 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    (by rw [(outV t6 G6 K.R.hi (fun q h => Or.inl (md h))).trans hb]
        exact sp.lc2 b s.basis t6.basis (fun q hq => (back6 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) hI2)
    ((outV t6 G6 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t6 G6 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t6 G6 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q2c r7 t6=t7 at st7 ⊢
  have F7 : ∀q,q∉K.R.dhi → q∉K.X2 → t7.basis q=t6.basis q := st7.2.2.2
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t7.basis q=s.basis q :=
    fun q h hS hT x => (F7 q (fun y => h (md y)) (fun y => x (x2 y))).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo t7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  -- clear a^2
  have st8 := sp.cl1 t7 r8
    (by rw [dlo7,(outV t7 G7 K.R.lo (fun q h => Or.inl (mt h))).trans ha])
    (by rw [(outV t7 G7 K.R.lo (fun q h => Or.inl (mt h))).trans ha]
        exact sp.lc1 a s.basis t7.basis (fun q hq => ((F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).trans (back6 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).symm) hI1)
    ((outV t7 G7 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t7 G7 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t7 G7 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q1c r8 t7=t8 at st8 ⊢
  have F8 : ∀q,q∉K.R.dlo → q∉K.X1 → t8.basis q=t7.basis q := st8.2.2.2
  have k78 (r : List Wire) (h : ∀q∈r,q∉K.R.dlo ∧ q∉K.X1 ∧ q∉K.R.dhi ∧ q∉K.X2) :
      regValue r t8.basis=regValue r t6.basis :=
    regValue_congr _ _ _ (fun q hq => (F8 q (h q hq).1 (h q hq).2.1).trans (F7 q (h q hq).2.2.1 (h q hq).2.2.2))
  refine ⟨st8.1.trans (st7.1.trans (st6.1.trans (st5.1.trans (st4.1.trans (st3.1.trans
    (st2.1.trans st1.1)))))),?_,?_,?_,?_,?_⟩
  · rw [K.R.dst_value w,st8.2.1,(regValue_congr _ _ _ (fun q hq => F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.1]; simp
  · rw [k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩)]; exact st6.2.1
  · rw [k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩)]; exact T6
  · rw [X,regValue_append,regValue_append,st8.2.2.1,
      (regValue_congr _ _ _ (fun q hq => F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.2.1,
      k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩),X56]; simp
  · intro q hd hT hx
    by_cases hS : q∈K.R.S
    · have a1 := (regValue_zero _ _).mp st6.2.1 q hS
      have a2 := (regValue_zero _ _).mp hS0 q hS
      rw [F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS),F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS),a1,a2]
    · exact (F8 q (fun y => hd (mt y)) (fun y => hx (x1 y))).trans (G7 q hd hS hT hx)


theorem make_counts (w : K.R.W) :
    toffoliCount (make K)+6+2*(if K.R.trimOK then 1 else 0)=toffoliCount K.Q1+toffoliCount K.Q2+toffoliCount K.Q5+(kextra K.R.bank.length K.R.h-(K.R.bank.length-K.R.h)) ∧
    measurementCount (make K)+(if K.R.trimOK then 1 else 0)=measurementCount K.Q1+measurementCount K.Q2+measurementCount K.Q5+
      kextra K.R.bank.length K.R.h := by
  have p := K.R.piece_counts w
  have z := K.R.scl1591_counts w
  have mz := K.R.m8z_counts w
  have mz7 := K.R.m7t_counts w
  have mk7 := K.R.m7k_counts w
  have mc6 := K.R.m6c_counts w
  have mk6 := K.R.m6k_counts w
  have mh6 := K.R.m6h_counts w
  have e : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6h++K.R.m7k++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have q1 := p.2.2.2.2.1
  have q2 := p.2.2.2.2.2.1
  simp only [toffoliCount_append,measurementCount_append] at q1 q2
  rw [e]
  simp only [toffoliCount_append,measurementCount_append,p.1,p.2.1,z.1,z.2,kextra]
  constructor <;> omega

theorem clear_counts (w : K.R.W) :
    toffoliCount (clear K)+5+(if K.R.trimOK then 1 else 0)=toffoliCount K.Q1c+toffoliCount K.Q2c+toffoliCount K.Q5c+(kextra K.R.bank.length K.R.h-(K.R.bank.length-K.R.h)) ∧
    measurementCount (clear K)+(if K.R.trimOK then 1 else 0)=measurementCount K.Q1c+measurementCount K.Q2c+measurementCount K.Q5c+
      kextra K.R.bank.length K.R.h := by
  have p := K.R.piece_counts w
  have z := K.R.scl1591_counts w
  have mc8 := K.R.c8z_counts w
  have mc7 := K.R.c7t_counts w
  have cc6 := K.R.c6c_counts w
  have ch6 := K.R.c6h_counts w
  have e : (clear K)=K.R.smk++(K.R.c8z++K.R.c7t++K.R.c6h)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have q1 := p.2.2.2.2.2.2.1
  have q2 := p.2.2.2.2.2.2.2
  simp only [toffoliCount_append,measurementCount_append] at q1 q2
  rw [e]
  simp only [toffoliCount_append,measurementCount_append,p.1,p.2.1,z.1,z.2,kextra]
  constructor <;> omega

theorem r_sub (q : Wire) (h : q∈K.R.all.toFinset) : q∈K.all.toFinset := by
  simp only [List.mem_toFinset,all,List.mem_append] at h ⊢; exact Or.inl h

theorem steps_support (w : K.R.W)
    (s1 : ECDSAAdd.wires K.Q1⊆K.all.toFinset) (s1c : ECDSAAdd.wires K.Q1c⊆K.all.toFinset)
    (s2 : ECDSAAdd.wires K.Q2⊆K.all.toFinset) (s2c : ECDSAAdd.wires K.Q2c⊆K.all.toFinset)
    (s5 : ECDSAAdd.wires K.Q5⊆K.all.toFinset) (s5c : ECDSAAdd.wires K.Q5c⊆K.all.toFinset) :
    ECDSAAdd.wires (make K)⊆K.all.toFinset ∧ ECDSAAdd.wires (clear K)⊆K.all.toFinset := by
  have p := K.R.piece_support w
  have sc := K.R.scl1591_support w
  have e1 : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6h++K.R.m7k++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have e2 : (clear K)=K.R.smk++(K.R.c8z++K.R.c7t++K.R.c6h)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have lift {P : Program} (h : ECDSAAdd.wires P⊆K.R.all.toFinset) : ECDSAAdd.wires P⊆K.all.toFinset :=
    fun q hq => K.r_sub q (h hq)
  have ap {P Q : Program} (h1 : ECDSAAdd.wires P⊆K.all.toFinset) (h2 : ECDSAAdd.wires Q⊆K.all.toFinset) :
      ECDSAAdd.wires (P++Q)⊆K.all.toFinset := by rw [wires_append]; exact Finset.union_subset h1 h2
  have pz : ECDSAAdd.wires (K.R.m6h++K.R.m7k++K.R.m8z)⊆K.R.all.toFinset := by
    have h := p.2.2.1
    simp only [wires_append,Finset.union_subset_iff] at h ⊢
    exact ⟨⟨K.R.m6h_support w h.1.1,(K.R.m7k_wires w).trans h.1.2⟩,(K.R.m8z_wires w).trans h.2⟩
  have cz : ECDSAAdd.wires (K.R.c8z++K.R.c7t++K.R.c6h)⊆K.R.all.toFinset := by
    have h := p.2.2.2.1
    simp only [wires_append,Finset.union_subset_iff] at h ⊢
    exact ⟨⟨(K.R.c8z_wires w).trans h.1.1,(K.R.c7t_wires).trans h.1.2⟩,(K.R.c6h_wires w).trans h.2⟩
  rw [e1,e2]
  exact ⟨ap (ap (ap (ap (ap s1 s2) (lift p.1)) s5) (lift pz)) (lift sc),
    ap (ap (ap (ap (ap (lift p.1) (lift cz)) s5c) (lift sc)) s2c) s1c⟩

theorem steps_physical (w : K.R.W) (hn : K.all.Nodup)
    (p1 : GatePhysical K.Q1) (p1c : GatePhysical K.Q1c) (p2 : GatePhysical K.Q2) (p2c : GatePhysical K.Q2c)
    (p5 : GatePhysical K.Q5) (p5c : GatePhysical K.Q5c) :
    GatePhysical (make K) ∧ GatePhysical (clear K) := by
  have p := K.R.piece_physical (K.rnd hn)
  have sc := K.R.scl1591_physical w (K.rnd hn)
  have e1 : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6h++K.R.m7k++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have e2 : (clear K)=K.R.smk++(K.R.c8z++K.R.c7t++K.R.c6h)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have pz : GatePhysical (K.R.m6h++K.R.m7k++K.R.m8z) := by
    have h := p.2.2.1
    simp only [gatePhysical_append] at h ⊢
    exact ⟨⟨K.R.m6h_physical w (K.rnd hn) h.1.1,K.R.m7k_physical w (K.rnd hn)⟩,K.R.m8z_physical (K.rnd hn)⟩
  have cz : GatePhysical (K.R.c8z++K.R.c7t++K.R.c6h) := by
    have h := p.2.2.2.1
    simp only [gatePhysical_append] at h ⊢
    exact ⟨⟨K.R.c8z_physical w (K.rnd hn),K.R.c7t_physical (K.rnd hn)⟩,K.R.c6h_physical w (K.rnd hn) h.2⟩
  rw [e1,e2]
  exact ⟨ap (ap (ap (ap (ap p1 p2) p.1) p5) pz) sc,ap (ap (ap (ap (ap p.1 cz) p5c) sc) p2c) p1c⟩

end ECDSAAdd.Entrant.LowZero18KG

namespace ECDSAAdd.Entrant.LowZero18KG
open Arithmetic KG
variable (K : KG)
theorem steps_slots2 (w : K.R.W) :
    Challenge.gateSlots (make K)+Challenge.gateSlots (clear K) ≤
      Challenge.gateSlots K.Q1+Challenge.gateSlots K.Q1c+Challenge.gateSlots K.Q2+Challenge.gateSlots K.Q2c+
      Challenge.gateSlots K.Q5+Challenge.gateSlots K.Q5c+
      (2*(Challenge.gateSlots K.R.smk+Challenge.gateSlots K.R.scl)+Challenge.gateSlots (K.R.m6++K.R.m7++K.R.m8)+
      Challenge.gateSlots (K.R.c8++K.R.c7++K.R.c6)) := by
  have ms := K.R.m8z_slots w
  have ms7 := K.R.m7k_slots w
  have ms6 := (K.R.m6h_slots w).trans (K.R.m6k_slots w)
  have mc8 := K.R.c8z_slots w
  have mc7 := K.R.c7t_slots
  have mc6 := K.R.c6h_slots w
  have sc := K.R.scl1591_slots
  simp only [make,clear,Challenge.gateSlots_append] at sc ⊢; omega
end ECDSAAdd.Entrant.LowZero18KG

namespace ECDSAAdd.Entrant.LowZero18KG
open Arithmetic
variable (K : KG)
attribute [local irreducible] toffoliCount measurementCount Challenge.gateSlots wires

theorem make_counts_old (w : K.R.W) :
    toffoliCount (make K)+6+2*(if K.R.trimOK then 1 else 0)=toffoliCount (FrontierSumCleanup1591KG.make K) ∧
    measurementCount (make K)+(if K.R.trimOK then 1 else 0)=measurementCount (FrontierSumCleanup1591KG.make K) := by
  have a := make_counts K w
  have b := FrontierSumCleanup1591KG.make_counts K w
  constructor <;> omega

theorem clear_counts_old (w : K.R.W) :
    toffoliCount (clear K)+5+(if K.R.trimOK then 1 else 0)=toffoliCount (FrontierSumCleanup1591KG.clear K) ∧
    measurementCount (clear K)+(if K.R.trimOK then 1 else 0)=measurementCount (FrontierSumCleanup1591KG.clear K) := by
  have a := clear_counts K w
  have b := FrontierSumCleanup1591KG.clear_counts K w
  constructor <;> omega

theorem make_support_subset (w : K.R.W) :
    wires (make K)⊆wires (FrontierSumCleanup1591KG.make K) := by
  have a6 := K.R.m6h_wires_smk w
  have a7 := K.R.m7k_wires w
  have a8 := K.R.m8z_wires w
  simp only [make,FrontierSumCleanup1591KG.make,wires_append]
  intro q hq
  have h6 := @a6 q
  have h7 := @a7 q
  have h8 := @a8 q
  simp only [Finset.mem_union] at hq h6 ⊢
  tauto

theorem clear_support_subset (w : K.R.W) :
    wires (clear K)⊆wires (FrontierSumCleanup1591KG.clear K) := by
  simp only [clear,FrontierSumCleanup1591KG.clear,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact K.R.c8z_wires w | exact K.R.c7t_wires | exact K.R.c6h_wires w | exact Finset.Subset.refl _

theorem make_slots_old (w : K.R.W) :
    Challenge.gateSlots (make K)≤Challenge.gateSlots (FrontierSumCleanup1591KG.make K) := by
  have a := K.R.m7t_slots
  have a7 := K.R.m7k_slots w
  have a8 := (K.R.m7k_res w).2.2.2.1
  have b := K.R.m8z_slots w
  have c := (K.R.m6h_slots w).trans (K.R.m6k_slots w)
  simp only [make,FrontierSumCleanup1591KG.make,Challenge.gateSlots_append]
  omega

theorem clear_slots_old (w : K.R.W) :
    Challenge.gateSlots (clear K)≤Challenge.gateSlots (FrontierSumCleanup1591KG.clear K) := by
  have a := K.R.c8z_slots w
  have b := K.R.c7t_slots
  have c := K.R.c6h_slots w
  simp only [clear,FrontierSumCleanup1591KG.clear,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.LowZero18KG
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18LowK =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18Core
-- consolidated import: import ECDSAAdd.Submission.Entrant.SquareCarryLoan719BFProof

-- DIAGONAL COMPONENT LowK.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
section
namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

/-- Fold-pad tail: untouched by the leaf producer and cleanup, used only for clean-at-rest scratch. -/
def ktmp (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.drop 131

def oregs (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=64,bank:=L.inputBank.take src.length,dst:=dst,
   S:=((ktmp L).take 66).take (src.length-63),
   T:=(ext.take 132).take (2*(src.length-63)),
   z:=(L.leafCarry.drop 193).take 62,
   pad:=L.leafPad,carry:=L.leafCarry.take 193,cin:=L.core.cin}

def iregs (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=32,bank:=(oregs L ext src dst).lo,dst:=(oregs L ext src dst).dlo,
   S:=((ktmp L).drop 66).take 33,T:=(ext.drop 132).take 66,
   z:=(oregs L ext src dst).z.take 30,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

def jregsH (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=32,bank:=(oregs L ext src dst).hi,dst:=(oregs L ext src dst).dhi,
   S:=((ext.drop 198).take 34).take 33,T:=(ext.drop 232).take 66,
   z:=(oregs L ext src dst).z.take 30,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

def jregsS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=33,bank:=(oregs L ext src dst).S,dst:=(oregs L ext src dst).T,
   S:=(ext.drop 198).take 34,T:=(ext.drop 232).take 68,
   z:=(oregs L ext src dst).z.take 31,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

/-- 128-bit leaves: nested split of the low and high halves, cleaned low inner sum. -/
def kgH (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=(jregsH L ext src dst).S++(jregsH L ext src dst).T,X5:=[],
   Q1:=LowZero18Diagonal.makeC (iregs L ext src dst),Q1c:=LowZero18Diagonal.clearC (iregs L ext src dst),
   Q2:=LowZero18Diagonal.make (jregsH L ext src dst),Q2c:=LowZero18Diagonal.clear (jregsH L ext src dst),
   Q5:=TrimMid.tsqM (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,Q5c:=TrimSquare4.tsqcM4 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,
   I1:=(iregs L ext src dst).invC,I2:=(jregsH L ext src dst).invF,I5:=fun _ _ => True}

/-- 129-bit leaf: nested split of the low half and of the sum square, cleaned low inner sum. -/
def kgS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=[],X5:=(jregsS L ext src dst).S++(jregsS L ext src dst).T,
   Q1:=LowZero18Diagonal.makeC (iregs L ext src dst),Q1c:=LowZero18Diagonal.clearC (iregs L ext src dst),
   Q2:=TrimMid.tsqM (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,Q2c:=TrimSquare4.tsqcM4 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,
   Q5:=LowZero18Diagonal.make (jregsS L ext src dst),Q5c:=LowZero18Diagonal.clear (jregsS L ext src dst),
   I1:=(iregs L ext src dst).invC,I2:=fun _ _ => True,I5:=(jregsS L ext src dst).invF}

def kg (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  if src.length=128 then kgH L ext src dst else kgS L ext src dst

theorem ktmp_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (ktmp L).length=123 := by
  simp [ktmp,L.foldPad_length hw]

theorem oregs_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (oregs L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [oregs,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl] <;> omega

theorem iregs_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (iregs L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [iregs,oregs,KRegs.lo,KRegs.dlo,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl] <;> omega

theorem jregsH_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : src.length=128) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (jregsH L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [jregsH,oregs,KRegs.hi,KRegs.dhi,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl,h128] <;> omega

theorem jregsS_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h129 : src.length=129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (jregsS L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [jregsS,oregs,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl,h129] <;> omega

theorem tmp_count (L : CuccaroStreamedSquareWideLayout) (n : Nat) (q : Wire) :
    (L.inputBank.take n++L.leafPad++L.leafCarry++ktmp L).count q≤
      L.core.work.count q+L.foldPad.count q := by
  have inputBound := (List.take_sublist n L.inputBank).count_le q
  have workSplit := congrArg (List.count q) (List.take_append_drop 129 L.core.work)
  have padSplit := congrArg (List.count q) (List.take_append_drop 1 L.foldPad)
  have tailSplit := congrArg (List.count q) (List.take_append_drop 130 (L.foldPad.drop 1))
  have hdd : (L.foldPad.drop 1).drop 130=L.foldPad.drop 131 := by simp [List.drop_drop]
  rw [hdd] at tailSplit
  simp only [inputBank,leafPad,leafCarry,ktmp,List.count_append] at inputBound workSplit padSplit tailSplit ⊢
  omega

def kbig2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) : List Wire :=
  (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++ktmp L)++ext

theorem lst_le2 (L : CuccaroStreamedSquareWideLayout) (control : Wire) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (q : Wire) :
    (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++ktmp L).count q ≤
      (control::L.wires).count q := by
  have a := hs q
  have b := hd q
  have banks := tmp_count L src.length q
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,List.count_cons,
    List.count_append,List.count_nil] at a banks ⊢
  omega

theorem kbig2_nodup (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (ext : List Wire) (hx : ext.Nodup)
    (hdx : ∀q∈ext,q∉control::L.wires) : (kbig2 L ext control src dst).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have b := List.nodup_iff_count_le_one.mp hx q
  have c := lst_le2 L control src dst hs hd q
  have d := List.nodup_iff_count_le_one.mp hn q
  simp only [kbig2,List.count_append] at c ⊢
  by_cases hq : q∈ext
  · have z : (control::L.wires).count q=0 := List.count_eq_zero.mpr (hdx q hq)
    omega
  · have z : ext.count q=0 := List.count_eq_zero.mpr hq
    omega

theorem ktmp_wires (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q∈ktmp L) : q∈L.wires := by
  have h' : q∈L.foldPad := List.mem_of_mem_drop h
  change q∈L.core.pad++L.overflowPad at h'
  change q∈L.core.wires++L.overflowPad
  rcases List.mem_append.mp h' with hp | he
  · apply List.mem_append_left _
    change q∈(((((L.core.y++L.core.out)++L.core.product)++L.core.pad)++L.core.work)++_)
    apply List.mem_append_left _
    apply List.mem_append_left _
    exact List.mem_append_right _ hp
  · exact List.mem_append_right _ he

theorem ext_split4 (ext : List Wire) (a b c : Nat) (q : Wire) :
    ((ext.take 132).take a).count q+((ext.drop 132).take 66).count q+
      (((ext.drop 198).take 34).take b).count q+((ext.drop 232).take c).count q≤ext.count q := by
  have x1 := kcnt_take (ext.take 132) a q
  have x2 := kcnt_take ((ext.drop 198).take 34) b q
  have x3 := kcnt_take (ext.drop 232) c q
  have e1 := kcnt_split ext 132 q
  have e2 := kcnt_split (ext.drop 132) 66 q
  have e3 := kcnt_split (ext.drop 198) 34 q
  have e4 := kcnt_take (ext.drop 132) 66 q
  simp only [List.drop_drop] at e2 e3
  norm_num at e2 e3
  omega

theorem tmp_split2 (L : CuccaroStreamedSquareWideLayout) (a : Nat) (q : Wire) :
    (((ktmp L).take 66).take a).count q+(((ktmp L).drop 66).take 33).count q≤(ktmp L).count q := by
  have x1 := kcnt_take ((ktmp L).take 66) a q
  have x2 := kcnt_take ((ktmp L).drop 66) 33 q
  have e := kcnt_split (ktmp L) 66 q
  omega

theorem carry_split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (L.leafCarry.take 193).count q+((L.leafCarry.drop 193).take 62).count q≤L.leafCarry.count q := by
  have x := kcnt_take (L.leafCarry.drop 193) 62 q
  have e := kcnt_split L.leafCarry 193 q
  omega

end ECDSAAdd.Entrant.LowZero18LowK

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs




theorem sub_of_count {l l' : List Wire} (h : ∀q,l.count q≤l'.count q) : l.toFinset⊆l'.toFinset := by
  intro q hq
  have a := List.count_pos_iff.mpr (List.mem_toFinset.mp hq)
  exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by have := h q; omega))

section Inst
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

include hn hs hd hx hdx in
theorem kgH_nodup : (kgH L ext src dst).all.Nodup :=
  knd (kbig2_nodup L control hn src dst hs hd ext hx hdx) (fun q => by
    have a := ext_split4 ext (2*(src.length-63)) 33 66 q
    have b := tmp_split2 L (src.length-63) q
    have c := carry_split L q
    simp only [KG.all,KG.X,kgH,KRegs.all,oregs,iregs,jregsH,kbig2,List.count_cons,List.count_append,List.count_nil] at a b c ⊢
    omega)

include hn hs hd hx hdx in
theorem kgS_nodup : (kgS L ext src dst).all.Nodup :=
  knd (kbig2_nodup L control hn src dst hs hd ext hx hdx) (fun q => by
    have a := ext_split4 ext (2*(src.length-63)) 34 68 q
    have b := tmp_split2 L (src.length-63) q
    have c := carry_split L q
    have e : List.count q (((ext.drop 198).take 34).take 34)=List.count q ((ext.drop 198).take 34) := by
      rw [List.take_take,Nat.min_self]
    simp only [KG.all,KG.X,kgS,KRegs.all,oregs,iregs,jregsS,kbig2,List.count_cons,List.count_append,List.count_nil] at a b c e ⊢
    omega)

theorem kgH_iall (q : Wire) :
    (iregs L ext src dst).all.count q≤(kgH L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgH,KRegs.all,iregs,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgH_jall (q : Wire) :
    (jregsH L ext src dst).all.count q≤(kgH L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgH,KRegs.all,jregsH,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgS_iall (q : Wire) :
    (iregs L ext src dst).all.count q≤(kgS L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgS,KRegs.all,iregs,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgS_jall (q : Wire) :
    (jregsS L ext src dst).all.count q≤(kgS L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 31 q
  simp only [KG.all,KG.X,kgS,KRegs.all,jregsS,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega

include hw h128 hsmax hlen he in
theorem kgH_spec (h : src.length=128) (hall : (kgH L ext src dst).all.Nodup) : (kgH L ext src dst).Spec := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
  have ni : (iregs L ext src dst).all.Nodup := knd hall (kgH_iall L ext src dst)
  have nj : (jregsH L ext src dst).all.Nodup := knd hall (kgH_jall L ext src dst)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hh := w.hh; have h4 := w.h4
  have n5 : ((oregs L ext src dst).cin::(oregs L ext src dst).S++(oregs L ext src dst).T++
      (oregs L ext src dst).pad++(oregs L ext src dst).carry).Nodup :=
    knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  exact ⟨w,LowZero18Diagonal.diag_sq_cl_make (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_cl_clear (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    LowZero18Diagonal.diag_sq_full_make (jregsH L ext src dst) wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_full_clear (jregsH L ext src dst) wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsH L ext src dst).invF_local,
    ECDSAAdd.Entrant.sq_mid_make (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    sq_mid4_clear (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    sq_plain_local⟩

include hw h128 hsmax hlen he in
theorem kgS_spec (h : src.length=129) (hall : (kgS L ext src dst).all.Nodup) : (kgS L ext src dst).Spec := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
  have ni : (iregs L ext src dst).all.Nodup := knd hall (kgS_iall L ext src dst)
  have nj : (jregsS L ext src dst).all.Nodup := knd hall (kgS_jall L ext src dst)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hh := w.hh; have h4 := w.h4
  have hdl := w.dst
  have n2 : ((oregs L ext src dst).cin::(oregs L ext src dst).hi++(oregs L ext src dst).dhi++
      (oregs L ext src dst).pad++(oregs L ext src dst).carry).Nodup :=
    knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  exact ⟨w,LowZero18Diagonal.diag_sq_cl_make (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_cl_clear (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    ECDSAAdd.Entrant.sq_mid_make (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_mid4_clear (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_plain_local,
    LowZero18Diagonal.diag_sq_full_make (jregsS L ext src dst) wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_full_clear (jregsS L ext src dst) wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsS L ext src dst).invF_local⟩

end Inst
end ECDSAAdd.Entrant.LowZero18LowK

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

section Inst3
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (he : 300≤ext.length)

attribute [local irreducible] toffoliCount measurementCount

include hw in
theorem oregs_lens (h : 128≤src.length) (h2 : src.length≤129) :
    (oregs L ext src dst).h=64 ∧ (oregs L ext src dst).bank.length=src.length := by
  have sz := L.measured_bank_widths hw
  refine ⟨rfl,?_⟩
  simp only [oregs,List.length_take,sz.1]; omega

include hw h128 hsmax hlen he in
theorem kgH_counts (h : src.length=128) :
    toffoliCount (LowZero18KG.make (kgH L ext src dst))=6565 ∧ measurementCount (LowZero18KG.make (kgH L ext src dst))=6681 ∧
    toffoliCount (LowZero18KG.clear (kgH L ext src dst))=6531 ∧ measurementCount (LowZero18KG.clear (kgH L ext src dst))=6681 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := LowZero18KG.make_counts (kgH L ext src dst) w
  have cl := LowZero18KG.clear_counts (kgH L ext src dst) w
  have i1 := LowZero18Diagonal.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := LowZero18Diagonal.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl1591_counts wi
  have j1 := LowZero18Diagonal.make_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have j2 := LowZero18Diagonal.clear_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have q := TrimSquare3.tsq3_counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsH L ext src dst).h=32 := rfl
  have pi : DiagSq.parR (iregs L ext src dst)=1 := by rw [DiagSq.parR_eq _ wi,il,ih]; decide
  have pj : DiagSq.parR (jregsH L ext src dst)=1 := by rw [DiagSq.parR_eq _ wj,jl,jh]; decide
  rw [pi] at i1 i2; rw [pj] at j1 j2
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)-11-1 ∧ measurementCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)-4-1+32 ∧
      toffoliCount (kgH L ext src dst).Q1c=(raw_kcost 64 32-30)-12-1 ∧ measurementCount (kgH L ext src dst).Q1c=32+((raw_kcost 64 32-30)-4-1) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [toffoliCount_append,ip0.1]; have := i1.1; omega
    · show measurementCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [measurementCount_append,ip0.2]; have := i1.2; omega
    · show toffoliCount ((iregs L ext src dst).smk++(LowZero18Diagonal.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]; norm_num [raw_kcost,raw_ksq,signedSquareRowsCount]
    · show measurementCount ((iregs L ext src dst).smk++(Z5Diagonal.clear (iregs L ext src dst)))=_; rw [measurementCount_append,ip.2.1]; have := i2.2; omega
  have t2 : toffoliCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30)-11-1 ∧ measurementCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30)-4-1 ∧
      toffoliCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30)-32-12-1 ∧ measurementCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30)-4-1 :=
    ⟨j1.1,j1.2,j2.1,by show measurementCount (Z5Diagonal.clear (jregsH L ext src dst))=_; have := j2.2; omega⟩
  have t5 : toffoliCount (kgH L ext src dst).Q5=ksq 65-2 ∧ measurementCount (kgH L ext src dst).Q5=ksq 65-2 ∧
      toffoliCount (kgH L ext src dst).Q5c=ksq 65-3 ∧ measurementCount (kgH L ext src dst).Q5c=ksq 65-2 := by
    have e : (oregs L ext src dst).S.length=65 := by omega
    have f : (oregs L ext src dst).T.length=130 := by omega
    have qm := TrimMid.tsqM_counts_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have q4 := TrimSquare4.tsqcM4_counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have k : signedSquareRowsCount 65+130-3=ksq 65-1 := rfl
    rw [e,f] at q
    rw [e,TrimMid.par_65] at qm
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (TrimMid.tsqM (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (TrimMid.tsqM (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show toffoliCount (TrimSquare4.tsqcM4 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (TrimSquare4.tsqcM4 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
  have rb : (kgH L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgH L ext src dst).R.h=64 := rfl
  have tk : ¬(kgH L ext src dst).R.trimOK := by
    show ¬(2*(kgH L ext src dst).R.h+1≤(kgH L ext src dst).R.bank.length); rw [rb,rh,h]; norm_num
  rw [if_neg tk,Nat.add_zero] at mk cl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  refine ⟨?_,?_,?_,?_⟩ <;> omega

include hw h128 hsmax hlen he in
theorem kgS_counts (h : src.length=129) :
    toffoliCount (LowZero18KG.make (kgS L ext src dst))=6679 ∧ measurementCount (LowZero18KG.make (kgS L ext src dst))=6797 ∧
    toffoliCount (LowZero18KG.clear (kgS L ext src dst))=6645 ∧ measurementCount (LowZero18KG.clear (kgS L ext src dst))=6797 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := LowZero18KG.make_counts (kgS L ext src dst) w
  have cl := LowZero18KG.clear_counts (kgS L ext src dst) w
  have i1 := LowZero18Diagonal.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := LowZero18Diagonal.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl1591_counts wi
  have j1 := LowZero18Diagonal.make_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have j2 := LowZero18Diagonal.clear_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have q := TrimSquare3.tsq3_counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsS L ext src dst).h=33 := rfl
  have pi : DiagSq.parR (iregs L ext src dst)=1 := by rw [DiagSq.parR_eq _ wi,il,ih]; decide
  have pj : DiagSq.parR (jregsS L ext src dst)=2 := by rw [DiagSq.parR_eq _ wj,jl,jh]; decide
  rw [pi] at i1 i2; rw [pj] at j1 j2
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)-11-1 ∧ measurementCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)-4-1+32 ∧
      toffoliCount (kgS L ext src dst).Q1c=(raw_kcost 64 32-30)-12-1 ∧ measurementCount (kgS L ext src dst).Q1c=32+((raw_kcost 64 32-30)-4-1) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [toffoliCount_append,ip0.1]; have := i1.1; omega
    · show measurementCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [measurementCount_append,ip0.2]; have := i1.2; omega
    · show toffoliCount ((iregs L ext src dst).smk++(LowZero18Diagonal.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]; norm_num [raw_kcost,raw_ksq,signedSquareRowsCount]
    · show measurementCount ((iregs L ext src dst).smk++(Z5Diagonal.clear (iregs L ext src dst)))=_; rw [measurementCount_append,ip.2.1]; have := i2.2; omega
  have t2 : toffoliCount (kgS L ext src dst).Q2=ksq 65-2 ∧ measurementCount (kgS L ext src dst).Q2=ksq 65-2 ∧
      toffoliCount (kgS L ext src dst).Q2c=ksq 65-3 ∧ measurementCount (kgS L ext src dst).Q2c=ksq 65-2 := by
    have e : (oregs L ext src dst).hi.length=65 := by omega
    have f : (oregs L ext src dst).dhi.length=130 := by omega
    have qm := TrimMid.tsqM_counts_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have q4 := TrimSquare4.tsqcM4_counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have k : signedSquareRowsCount 65+130-3=ksq 65-1 := rfl
    rw [e,f] at q
    rw [e,TrimMid.par_65] at qm
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (TrimMid.tsqM (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (TrimMid.tsqM (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show toffoliCount (TrimSquare4.tsqcM4 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (TrimSquare4.tsqcM4 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
  have t5 : toffoliCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31)-11-2 ∧ measurementCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31)-4-2 ∧
      toffoliCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31)-33-12-2 ∧ measurementCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31)-4-2 :=
    ⟨j1.1,j1.2,j2.1,by show measurementCount (Z5Diagonal.clear (jregsS L ext src dst))=_; have := j2.2; omega⟩
  have rb : (kgS L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgS L ext src dst).R.h=64 := rfl
  have tk : (kgS L ext src dst).R.trimOK := by
    show 2*(kgS L ext src dst).R.h+1≤(kgS L ext src dst).R.bank.length; rw [rb,rh,h]
  rw [if_pos tk] at mk cl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  refine ⟨?_,?_,?_,?_⟩ <;> omega

end Inst3
end ECDSAAdd.Entrant.LowZero18LowK

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

section Inst4
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

theorem kg_R : (kg L ext src dst).R=oregs L ext src dst := by
  unfold kg; split <;> rfl

theorem kg_I1 : (kg L ext src dst).I1=(iregs L ext src dst).invC := by
  unfold kg; split <;> rfl

theorem kg_X (q : Wire) (h : q∈(kg L ext src dst).X) : q∈ext ∨ q∈((ktmp L).drop 66).take 33 := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · rcases List.mem_append.mp h with h|h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take (h : q∈((ext.drop 198).take 34).take 33))))
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 66)))
    · exact absurd h (List.not_mem_nil)
  · rw [kg,if_neg c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · exact absurd h (List.not_mem_nil)
    · rcases List.mem_append.mp h with h|h
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 198).take 34)))
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 68)))

include hn hs hd hx hdx in
theorem kg_nodup : (kg L ext src dst).all.Nodup := by
  by_cases c : src.length=128
  · rw [kg,if_pos c]; exact kgH_nodup L control hn ext src dst hs hd hx hdx
  · rw [kg,if_neg c]; exact kgS_nodup L control hn ext src dst hs hd hx hdx

include hw h128 hsmax hlen he in
theorem kg_spec (hall : (kg L ext src dst).all.Nodup) : (kg L ext src dst).Spec := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at hall ⊢; exact kgH_spec L hw ext src dst h128 hsmax hlen he c hall
  · rw [kg,if_neg c] at hall ⊢; exact kgS_spec L hw ext src dst h128 hsmax hlen he (by omega) hall

def lowkcost2 (n : Nat) : Nat := if n=128 then 6681 else 6797
def lowkcostTMake (n : Nat) : Nat := if n=128 then 6565 else 6679
def lowkcostTClear (n : Nat) : Nat := if n=128 then 6531 else 6645
def lowkcostTPair (n : Nat) : Nat := lowkcostTMake n+lowkcostTClear n

include hw h128 hsmax hlen he in
theorem kg_counts :
    toffoliCount (LowZero18KG.make (kg L ext src dst))=lowkcostTMake src.length ∧
    measurementCount (LowZero18KG.make (kg L ext src dst))=lowkcost2 src.length ∧
    toffoliCount (LowZero18KG.clear (kg L ext src dst))=lowkcostTClear src.length ∧
    measurementCount (LowZero18KG.clear (kg L ext src dst))=lowkcost2 src.length := by
  by_cases c : src.length=128
  · simp only [kg,lowkcost2,lowkcostTMake,lowkcostTClear,if_pos c]; exact kgH_counts L hw ext src dst h128 hsmax hlen he c
  · simp only [kg,lowkcost2,lowkcostTMake,lowkcostTClear,if_neg c]; exact kgS_counts L hw ext src dst h128 hsmax hlen he (by omega)

include hw h128 hsmax hlen he in
theorem kg_support :
    ECDSAAdd.wires (LowZero18KG.make (kg L ext src dst))⊆(kg L ext src dst).all.toFinset ∧
    ECDSAAdd.wires (LowZero18KG.clear (kg L ext src dst))⊆(kg L ext src dst).all.toFinset := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have rp := (oregs L ext src dst).piece_support w
  have ip := (iregs L ext src dst).piece_support wi
  have is := LowZero18Diagonal.steps_support (iregs L ext src dst) wi
  have isc := (iregs L ext src dst).scl1591_support wi
  have tr {P : Program} {A B : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : A⊆B) : ECDSAAdd.wires P⊆B := h1.trans h2
  have ap {P Q : Program} {A : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : ECDSAAdd.wires Q⊆A) :
      ECDSAAdd.wires (P++Q)⊆A := by rw [wires_append]; exact Finset.union_subset h1 h2
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have js := LowZero18Diagonal.steps_support (jregsH L ext src dst) wj
    have iK := sub_of_count (kgH_iall L ext src dst)
    have jK := sub_of_count (kgH_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgH L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact LowZero18KG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr js.1 jK) (tr js.2 jK) (tr ((TrimMid.tsqM_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1.trans rp.2.2.2.2.2.2.1) rK) (tr (((TrimSquare4.tsqcM4_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).trans (TrimMid.tsqM_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).2).trans rp.2.2.2.2.2.2.2) rK)
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have js := LowZero18Diagonal.steps_support (jregsS L ext src dst) wj
    have iK := sub_of_count (kgS_iall L ext src dst)
    have jK := sub_of_count (kgS_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgS L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact LowZero18KG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr ((TrimMid.tsqM_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1.trans rp.2.2.2.2.1) rK) (tr (((TrimSquare4.tsqcM4_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).trans (TrimMid.tsqM_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).2).trans rp.2.2.2.2.2.1) rK) (tr js.1 jK) (tr js.2 jK)

include hw h128 hsmax hlen he in
theorem kg_physical (hall : (kg L ext src dst).all.Nodup) :
    GatePhysical (LowZero18KG.make (kg L ext src dst)) ∧ GatePhysical (LowZero18KG.clear (kg L ext src dst)) := by
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  by_cases h : src.length=128
  · rw [kg,if_pos h] at hall ⊢
    have wj := jregsH_W L hw ext src dst h hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgH_iall L ext src dst)
    have nj := knd hall (kgH_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := LowZero18Diagonal.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl1591_physical wi ni
    have js := LowZero18Diagonal.steps_physical (jregsH L ext src dst) wj nj
    exact LowZero18KG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ip.1 is.2) js.1 js.2 (TrimMid.tsqM_physical_of (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2).1 (TrimSquare4.tsqcM4_physical (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (TrimMid.tsqM_physical_of (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2).2)
  · rw [kg,if_neg h] at hall ⊢
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgS_iall L ext src dst)
    have nj := knd hall (kgS_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := LowZero18Diagonal.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl1591_physical wi ni
    have js := LowZero18Diagonal.steps_physical (jregsS L ext src dst) wj nj
    exact LowZero18KG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ip.1 is.2) (TrimMid.tsqM_physical_of (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.1 rp.2.2.2.2.2.1).1 (TrimSquare4.tsqcM4_physical (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (TrimMid.tsqM_physical_of (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.1 rp.2.2.2.2.2.1).2) js.1 js.2

include hw h128 hsmax hlen he in
theorem kg_slots :
    Challenge.gateSlots (LowZero18KG.make (kg L ext src dst))+Challenge.gateSlots (LowZero18KG.clear (kg L ext src dst))≤1200000 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have ol := oregs_lens L hw ext src dst h128 hsmax
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T
  have ad := (oregs L ext src dst).adder_slots w rfl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have it := LowZero18Diagonal.tiny_slots (iregs L ext src dst) wi (by rw [il,ih]) (by rw [ih]; omega)
  simp only [LowZero18Diagonal.clear] at it
  have oldit := (iregs L ext src dst).tiny_slots wi (by rw [ih]; omega) (by rw [il,ih]; omega) (by omega)
  have isb := (iregs L ext src dst).make_sub_slots wi
  have isc := (iregs L ext src dst).scl1591_slots
  have g2 := TrimMid.tsqM_gateSlots_le (oregs L ext src dst).hi (oregs L ext src dst).dhi
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g2' := TrimSquare4.tsqcM4_slots (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g5 := TrimMid.tsqM_gateSlots_le (oregs L ext src dst).S (oregs L ext src dst).T
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g5' := TrimSquare4.tsqcM4_slots (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have x2 : (oregs L ext src dst).hi.length*(12*((oregs L ext src dst).hi.length+1)+6*(oregs L ext src dst).dhi.length) ≤ 65*(12*66+6*130) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x5 : (oregs L ext src dst).S.length*(12*((oregs L ext src dst).S.length+1)+6*(oregs L ext src dst).T.length) ≤ 66*(12*67+6*132) :=
    Nat.mul_le_mul (by omega) (by omega)
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
    have jh : (jregsH L ext src dst).h=32 := rfl
    have jt := LowZero18Diagonal.tiny_slots (jregsH L ext src dst) wj (by rw [jl,jh]) (by omega)
    simp only [LowZero18Diagonal.clear] at jt
    have st := LowZero18KG.steps_slots2 (kgH L ext src dst) w
    simp only [kgH,LowZero18Diagonal.makeC,LowZero18Diagonal.clearC,LowZero18Diagonal.clear,Z5Diagonal.clearC,KRegs.m5,KRegs.c5,Challenge.gateSlots_append] at st ad ⊢
    omega
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
    have jh : (jregsS L ext src dst).h=33 := rfl
    have jt := LowZero18Diagonal.tiny_slots (jregsS L ext src dst) wj (by rw [jl,jh]) (by omega)
    simp only [LowZero18Diagonal.clear] at jt
    have st := LowZero18KG.steps_slots2 (kgS L ext src dst) w
    simp only [kgS,LowZero18Diagonal.makeC,LowZero18Diagonal.clearC,LowZero18Diagonal.clear,Z5Diagonal.clearC,KRegs.m2,KRegs.c2,Challenge.gateSlots_append] at st ad ⊢
    omega

end Inst4
end ECDSAAdd.Entrant.LowZero18LowK


namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem kg_metadata (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    (kg L ext src dst).R=(FrontierSumCleanup1591LowK.kg L ext src dst).R ∧
    (kg L ext src dst).X1=(FrontierSumCleanup1591LowK.kg L ext src dst).X1 ∧
    (kg L ext src dst).X=(FrontierSumCleanup1591LowK.kg L ext src dst).X ∧
    (kg L ext src dst).all=(FrontierSumCleanup1591LowK.kg L ext src dst).all := by
  by_cases h : src.length=128
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true];exact ⟨rfl,rfl,rfl,rfl⟩
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false];exact ⟨rfl,rfl,rfl,rfl⟩

theorem kg_Q1c_subset (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    wires (kg L ext src dst).Q1c⊆wires (FrontierSumCleanup1591LowK.kg L ext src dst).Q1c := by
  have a := LowZero18Diagonal.clearC_support_subset (iregs L ext src dst)
  by_cases h : src.length=128
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,kgH,FrontierSumCleanup1591LowK.kgH] using a
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,kgS,FrontierSumCleanup1591LowK.kgS] using a

theorem kg_Q1_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (kg L ext src dst).Q1⊆wires (FrontierSumCleanup1591LowK.kg L ext src dst).Q1 := by
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have a := LowZero18Diagonal.makeC_support_subset (iregs L ext src dst) wi
  by_cases h : src.length=128
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,kgH,FrontierSumCleanup1591LowK.kgH] using a
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,kgS,FrontierSumCleanup1591LowK.kgS] using a

theorem kg_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (LowZero18KG.make (kg L ext src dst))+32+3*(if src.length=128 then 0 else 1)=
      toffoliCount (FrontierSumCleanup1591KG.make (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    measurementCount (LowZero18KG.make (kg L ext src dst))+12+2*(if src.length=128 then 0 else 1)=
      measurementCount (FrontierSumCleanup1591KG.make (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    toffoliCount (LowZero18KG.clear (kg L ext src dst))+34+2*(if src.length=128 then 0 else 1)=
      toffoliCount (FrontierSumCleanup1591KG.clear (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    measurementCount (LowZero18KG.clear (kg L ext src dst))+12+2*(if src.length=128 then 0 else 1)=
      measurementCount (FrontierSumCleanup1591KG.clear (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have a := kg_counts L hw ext src dst h128 h129 hd he
  have b := FrontierSumCleanup1591LowK.kg_counts L hw ext src dst h128 h129 hd he
  by_cases h : src.length=128
  all_goals simp only [lowkcostTMake,lowkcostTClear,lowkcost2,FrontierSumCleanup1591LowK.lowkcostTMake,
    FrontierSumCleanup1591LowK.lowkcostTClear,FrontierSumCleanup1591LowK.lowkcost2,h,ite_true,ite_false] at a b ⊢
  all_goals exact ⟨by omega,by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.LowZero18LowK

end


namespace ECDSAAdd.Entrant.CodexBorrowedUnion

/-- The borrowed controls of E already occur in the retained C segment. -/
theorem eight {α : Type} [DecidableEq α]
    {a b c d e f g h A B D E F G : Finset α}
    (ha : a ⊆ A) (hb : b ⊆ B) (hd : d ⊆ D)
    (he : e ⊆ E ∪ c) (hf : f ⊆ F) (hg : g ⊆ G) :
    a ∪ b ∪ c ∪ d ∪ e ∪ f ∪ g ∪ h ⊆
      A ∪ B ∪ c ∪ D ∪ E ∪ F ∪ G ∪ h := by
  intro q hq
  simp only [Finset.mem_union] at hq ⊢
  rcases hq with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (ha h)))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (hb h)))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (hd h)))))
  · rcases Finset.mem_union.mp (he h) with h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inr (hf h)))
  · exact Or.inl (Or.inr (hg h))
  · exact Or.inr h

theorem seven {α : Type} [DecidableEq α]
    {b c d e f g h B D E F G : Finset α}
    (hb : b ⊆ B) (hd : d ⊆ D)
    (he : e ⊆ E ∪ c) (hf : f ⊆ F) (hg : g ⊆ G) :
    b ∪ c ∪ d ∪ e ∪ f ∪ g ∪ h ⊆
      B ∪ c ∪ D ∪ E ∪ F ∪ G ∪ h := by
  simpa only [Finset.union_self] using
    eight (a := b) (A := B) (h := h) hb hb hd he hf hg

end ECDSAAdd.Entrant.CodexBorrowedUnion

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] wires toffoliCount measurementCount Challenge.gateSlots

theorem loan_make_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    wires (LowZero18KG.make (SquareCarryLoan719.patchKG L (kg L ext src dst)))⊆
      wires (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have ip := OneFlagReplay.rename_subset (SquareCarryLoan719.earlyPerm L) _ _
    (LowZero18Diagonal.makeC_support_subset (iregs L ext src dst) wi)
  have ro : FrontierSumCleanup1591LowK.oregs L ext src dst = oregs L ext src dst := rfl
  have ri : FrontierSumCleanup1591LowK.iregs L ext src dst = iregs L ext src dst := rfl
  have a6 := (oregs L ext src dst).m6h_wires_smk w
  have a7 := (oregs L ext src dst).m7k_wires w
  have a8 := (oregs L ext src dst).m8z_wires w
  by_cases h : src.length=128
  · have jp := LowZero18Diagonal.make_support_subset (jregsH L ext src dst)
      (jregsH_W L hw ext src dst h hd he)
    have rj : FrontierSumCleanup1591LowK.jregsH L ext src dst = jregsH L ext src dst := rfl
    have q5 := (TrimMid.tsqM_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,wires_append,ro,ri,rj]
    exact CodexBorrowedUnion.eight ip jp q5 a6 a7 a8
  · have jp := LowZero18Diagonal.make_support_subset (jregsS L ext src dst)
      (jregsS_W L hw ext src dst (by omega) hd he)
    have rj : FrontierSumCleanup1591LowK.jregsS L ext src dst = jregsS L ext src dst := rfl
    have q2 := (TrimMid.tsqM_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,wires_append,ro,ri,rj]
    exact CodexBorrowedUnion.eight ip q2 jp a6 a7 a8

theorem loan_clear_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    wires (LowZero18KG.clear (SquareCarryLoan719.patchKG L (kg L ext src dst)))⊆
      wires (SquareCarryLoan719BF.clear L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have ipc := OneFlagReplay.rename_subset (SquareCarryLoan719.earlyPerm L) _ _
    (LowZero18Diagonal.clearC_support_subset (iregs L ext src dst))
  have jhc := LowZero18Diagonal.clear_support_subset (jregsH L ext src dst)
  have jsc := LowZero18Diagonal.clear_support_subset (jregsS L ext src dst)
  by_cases h : src.length=128
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.clear,
      SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.c5,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact ipc | exact jhc | exact (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact (TrimSquare4.tsqcM4_wires_le _ _ _ _ _).trans (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact (oregs L ext src dst).c8z_wires w |
      exact (oregs L ext src dst).c7t_wires | exact (oregs L ext src dst).c6h_wires w | exact Finset.Subset.refl _
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.clear,
      SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.c2,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact ipc | exact jsc | exact (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact (TrimSquare4.tsqcM4_wires_le _ _ _ _ _).trans (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact (oregs L ext src dst).c8z_wires w |
      exact (oregs L ext src dst).c7t_wires | exact (oregs L ext src dst).c6h_wires w | exact Finset.Subset.refl _

theorem loan_make_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18KG.make (SquareCarryLoan719.patchKG L (kg L ext src dst)))≤
      Challenge.gateSlots (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have ip := LowZero18Diagonal.makeC_slots_old (iregs L ext src dst) wi
  have a := (oregs L ext src dst).m7t_slots
  have a7 := (oregs L ext src dst).m7k_slots w
  have b := (oregs L ext src dst).m8z_slots w
  have c6 := ((oregs L ext src dst).m6h_slots w).trans ((oregs L ext src dst).m6k_slots w)
  have q5 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have ro : oregs L ext src dst=FrontierSumCleanup1591LowK.oregs L ext src dst := rfl
  have ri : iregs L ext src dst=FrontierSumCleanup1591LowK.iregs L ext src dst := rfl
  by_cases h : src.length=128
  · have jp := LowZero18Diagonal.make_slots_le (jregsH L ext src dst)
      (jregsH_W L hw ext src dst h hd he)
    have rj : jregsH L ext src dst=FrontierSumCleanup1591LowK.jregsH L ext src dst := rfl
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,Challenge.gateSlots_append,Baselines.rename_gateSlots]
    simp only [ro,ri,rj] at ip a a7 b c6 jp q5 ⊢
    omega
  · have jp := LowZero18Diagonal.make_slots_le (jregsS L ext src dst)
      (jregsS_W L hw ext src dst (by omega) hd he)
    have rj : jregsS L ext src dst=FrontierSumCleanup1591LowK.jregsS L ext src dst := rfl
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,Challenge.gateSlots_append,Baselines.rename_gateSlots]
    simp only [ro,ri,rj] at ip a a7 b c6 jp q2 ⊢
    omega

theorem loan_clear_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18KG.clear (SquareCarryLoan719.patchKG L (kg L ext src dst)))≤
      Challenge.gateSlots (SquareCarryLoan719BF.clear L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have a := (oregs L ext src dst).c8z_slots w
  have b := (oregs L ext src dst).c7t_slots
  have c6 := (oregs L ext src dst).c6h_slots w
  have q5 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q5' := TrimSquare4.tsqcM4_slots (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2' := TrimSquare4.tsqcM4_slots (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have i1 := LowZero18Diagonal.clearC_slots_old (iregs L ext src dst)
  have jh := LowZero18Diagonal.clear_slots_old (jregsH L ext src dst)
  have js := LowZero18Diagonal.clear_slots_old (jregsS L ext src dst)
  have ro : oregs L ext src dst=FrontierSumCleanup1591LowK.oregs L ext src dst := rfl
  have ri : iregs L ext src dst=FrontierSumCleanup1591LowK.iregs L ext src dst := rfl
  have rh : jregsH L ext src dst=FrontierSumCleanup1591LowK.jregsH L ext src dst := rfl
  have rs : jregsS L ext src dst=FrontierSumCleanup1591LowK.jregsS L ext src dst := rfl
  by_cases h : src.length=128
  all_goals simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,ite_false,LowZero18KG.clear,
    SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
    kgH,kgS,FrontierSumCleanup1591LowK.kgH,FrontierSumCleanup1591LowK.kgS,
    LowZero18Diagonal.clearC,LowZero18Diagonal.clear,KRegs.c5,KRegs.c2,Challenge.gateSlots_append,Baselines.rename_gateSlots]
  all_goals simp only [LowZero18Diagonal.clearC,LowZero18Diagonal.clear,ro,ri,rh,rs] at a b c6 q5 q2 q5' q2' i1 jh js ⊢
  all_goals omega

end ECDSAAdd.Entrant.LowZero18LowK
end -- original module boundary


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end
