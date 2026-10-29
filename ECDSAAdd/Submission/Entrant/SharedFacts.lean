import ECDSAAdd.Submission.Entrant.SharedPoint

/-! Resources, support, physical validity and flag-level Hoare triples of the
shared point tests. -/
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout

theorem zeroWith_counts (Q : Program) (c : Wire) (bs : List ZeroBit) :
    toffoliCount (zeroWith Q c bs) = bs.length + toffoliCount Q ∧
    measurementCount (zeroWith Q c bs) = bs.length + measurementCount Q := by
  induction bs generalizing c with
  | nil => simp [zeroWith]
  | cons b bs ih =>
    simp only [zeroWith, toffoliCount_append, measurementCount_append, (ih b.work).1, (ih b.work).2]
    simp [nAnd, nAndErase, toffoliCount, measurementCount]
    omega

theorem zeroWith_wires (Q : Program) (c : Wire) (bs : List ZeroBit) :
    wires (zeroWith Q c bs) ⊆ (chainWires c bs).toFinset ∪ wires Q := by
  induction bs generalizing c with
  | nil => intro q hq; exact Finset.mem_union_right _ hq
  | cons b bs ih =>
    intro q hq
    simp only [zeroWith, wires_append, Finset.mem_union] at hq
    have hsub : (chainWires b.work bs).toFinset ⊆ (chainWires c (b::bs)).toFinset := by
      intro w hw
      simp only [chainWires, List.mem_toFinset, List.mem_cons, List.flatMap_cons, List.mem_append,
        ZeroBit.wires, List.not_mem_nil, or_false] at hw ⊢
      tauto
    rcases hq with (h | h) | h
    · simp [nAnd, wires, Instr.wires, chainWires, ZeroBit.wires] at h ⊢
      tauto
    · rcases Finset.mem_union.mp (ih b.work h) with h' | h'
      · exact Finset.mem_union_left _ (hsub h')
      · exact Finset.mem_union_right _ h'
    · simp [nAndErase, wires, Instr.wires, correctionWires, chainWires, ZeroBit.wires] at h ⊢
      tauto

theorem zeroWith_physical (Q : Program) (hQ : GatePhysical Q) (c : Wire) (bs : List ZeroBit)
    (hnd : (chainWires c bs).Nodup) : GatePhysical (zeroWith Q c bs) := by
  induction bs generalizing c with
  | nil => exact hQ
  | cons b bs ih =>
    have hn : (c::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or] at hn
    simp only [zeroWith, gatePhysical_append]
    refine ⟨⟨?_, ih b.work (List.nodup_cons.mpr ⟨hn.2.2.1, hn.2.2.2⟩)⟩, ?_⟩
    · intro i hi
      simp only [nAnd, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact trivial
      · exact ⟨hn.1.2.1, hn.2.1.1⟩
      · exact trivial
    · intro i hi
      simp only [nAndErase, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> exact trivial

theorem zeroWith_gateSlots (Q : Program) (c : Wire) (bs : List ZeroBit) :
    Challenge.gateSlots (zeroWith Q c bs) = 7 * bs.length + Challenge.gateSlots Q := by
  induction bs generalizing c with
  | nil => simp [zeroWith]
  | cons b bs ih =>
    simp only [zeroWith, Challenge.gateSlots_append, ih]
    simp [nAnd, nAndErase, Challenge.gateSlots, Challenge.instructionSlots]
    omega

theorem preMid_mem (k e tk tc : Wire) (kSplit cSplit : Bool) :
    ∀ q ∈ wires (preMid k e tk tc kSplit cSplit), q = k ∨ q = e ∨ q = tk ∨ q = tc := by
  intro q hq
  cases kSplit <;> cases cSplit <;> simp [preMid, wires, Instr.wires] at hq <;> tauto

theorem preMid_physical (k e tk tc : Wire) (kSplit cSplit : Bool) (hec : e ≠ tc) (hk : k ≠ tk)
    (het : e ≠ tk) : GatePhysical (preMid k e tk tc kSplit cSplit) := by
  intro i hi
  cases kSplit <;> cases cSplit <;>
    simp only [preMid, Bool.false_eq_true, if_false, if_true, List.nil_append, List.append_nil,
      List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  all_goals (rcases hi with rfl | rfl <;> first | exact hec | exact ⟨hk, het⟩)

section
variable (L : ControlledPointLayout) (hw : L.Widths)
include hw

theorem sharedPoint_counts (k tk tc : Wire) (cx cy : Fp) (kSplit cSplit : Bool) :
    toffoliCount (sharedPoint L k tk tc cx cy kSplit cSplit) = 514 + (if kSplit then 1 else 0) ∧
    measurementCount (sharedPoint L k tk tc cx cy kSplit cSplit) = 513 := by
  have ox := ptXB_length L hw
  have oy := ptYB_length L hw
  have z1 := zeroWith_counts (innerMid k (chainLast (chainLast L.control (ptXB L)) (ptYB L)) tk tc)
    (chainLast L.control (ptXB L)) (ptYB L)
  have z2 := zeroWith_counts (preMid k (chainLast L.control (ptXB L)) tk tc kSplit cSplit ++
    zeroWith (innerMid k (chainLast (chainLast L.control (ptXB L)) (ptYB L)) tk tc)
      (chainLast L.control (ptXB L)) (ptYB L)) L.control (ptXB L)
  have pm : toffoliCount (preMid k (chainLast L.control (ptXB L)) tk tc kSplit cSplit) =
      (if kSplit then 1 else 0) ∧
      measurementCount (preMid k (chainLast L.control (ptXB L)) tk tc kSplit cSplit) = 0 := by
    cases kSplit <;> cases cSplit <;> simp [preMid, toffoliCount, measurementCount]
  have im : toffoliCount (innerMid k (chainLast (chainLast L.control (ptXB L)) (ptYB L)) tk tc) = 1 ∧
      measurementCount (innerMid k (chainLast (chainLast L.control (ptXB L)) (ptYB L)) tk tc) = 0 := by
    simp [innerMid, toffoliCount, measurementCount]
  have pm2 := (show toffoliCount (preMid k (chainLast L.control (ptXB L)) tk tc kSplit cSplit ++
    zeroWith (innerMid k (chainLast (chainLast L.control (ptXB L)) (ptYB L)) tk tc)
      (chainLast L.control (ptXB L)) (ptYB L)) = _ from toffoliCount_append _ _)
  have pm3 := (show measurementCount (preMid k (chainLast L.control (ptXB L)) tk tc kSplit cSplit ++
    zeroWith (innerMid k (chainLast (chainLast L.control (ptXB L)) (ptYB L)) tk tc)
      (chainLast L.control (ptXB L)) (ptYB L)) = _ from measurementCount_append _ _)
  rw [pm2] at z2; rw [pm3] at z2
  simp only [sharedPoint, sharedBlock, toffoliCount_append, measurementCount_append,
    (xorConstant_counts _ _).1, (xorConstant_counts _ _).2]
  rw [z2.1, z2.2]
  rw [z1.1, z1.2, pm.1, pm.2, im.1, im.2, ox, oy]
  constructor <;> omega

theorem sharedPoint_wires (k tk tc : Wire) (cx cy : Fp) (kSplit cSplit : Bool) :
    wires (sharedPoint L k tk tc cx cy kSplit cSplit) ⊆
      (k :: tk :: tc :: L.control :: (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513)).toFinset := by
  set S := (k :: tk :: tc :: L.control :: (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513)).toFinset with hS
  have sk : k ∈ S := by simp [S]
  have stk : tk ∈ S := by simp [S]
  have stc : tc ∈ S := by simp [S]
  have sc : L.control ∈ S := by simp [S]
  have sp : ∀ q ∈ PointAddLayout.pointWires L.point, q ∈ S := fun q h => by simp [S, h]
  have sw : ∀ q ∈ L.dialogPool.take 513, q ∈ S := fun q h => by simp [S, h]
  have hXw : ∀ q ∈ (ptXB L).flatMap ZeroBit.wires, q ∈ S := by
    intro q hq
    have hp := (zeroPorts_perm (L.point.finite :: L.point.x) (L.dialogPool.take 257)
      (by simp [(point_lengths L hw).1, L.dialogPool_length hw])).mem_iff.mp hq
    rcases List.mem_append.mp hp with h | h
    · exact sp q (by simp only [PointAddLayout.pointWires, List.mem_append]; exact Or.inl h)
    · exact sw q (by rw [← pool_split L]; exact List.mem_append_left _ h)
  have hYw : ∀ q ∈ (ptYB L).flatMap ZeroBit.wires, q ∈ S := by
    intro q hq
    have hp := (zeroPorts_perm L.point.y ((L.dialogPool.take 513).drop 257)
      (by simp [(point_lengths L hw).2, L.dialogPool_length hw])).mem_iff.mp hq
    rcases List.mem_append.mp hp with h | h
    · exact sp q (by simp only [PointAddLayout.pointWires, List.mem_append]; exact Or.inr h)
    · exact sw q (by rw [← pool_split L]; exact List.mem_append_right _ h)
  have hin (bs : List ZeroBit) (h : ∀ q ∈ bs.flatMap ZeroBit.wires, q ∈ S) :
      ∀ q ∈ bs.map ZeroBit.input, q ∈ S := by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
    exact h _ (List.mem_flatMap.mpr ⟨b, hb, by simp [ZeroBit.wires]⟩)
  have xsub (bs : List ZeroBit) (h : ∀ q ∈ bs.flatMap ZeroBit.wires, q ∈ S) (kk : Nat) :
      wires (xorConstant (bs.map ZeroBit.input) kk) ⊆ S :=
    fun q hq => hin bs h q (List.mem_toFinset.mp (xorConstant_wires_subset _ _ hq))
  have chX : ∀ w ∈ chainWires L.control (ptXB L), w ∈ S := by
    intro w hw'
    simp only [chainWires, List.mem_cons] at hw'
    rcases hw' with rfl | h
    · exact sc
    · exact hXw w h
  have se : chainLast L.control (ptXB L) ∈ S := chX _ (chainLast_mem _ _)
  have chY : ∀ w ∈ chainWires (chainLast L.control (ptXB L)) (ptYB L), w ∈ S := by
    intro w hw'
    simp only [chainWires, List.mem_cons] at hw'
    rcases hw' with rfl | h
    · exact se
    · exact hYw w h
  have su : chainLast (chainLast L.control (ptXB L)) (ptYB L) ∈ S := chY _ (chainLast_mem _ _)
  have zsub (Q : Program) (c : Wire) (bs : List ZeroBit) (hc : ∀ w ∈ chainWires c bs, w ∈ S)
      (hQ : wires Q ⊆ S) : wires (zeroWith Q c bs) ⊆ S := by
    intro q hq
    rcases Finset.mem_union.mp (zeroWith_wires Q c bs hq) with h | h
    · exact hc q (List.mem_toFinset.mp h)
    · exact hQ h
  have pre : wires (preMid k (chainLast L.control (ptXB L)) tk tc kSplit cSplit) ⊆ S := by
    intro q hq
    rcases preMid_mem _ _ _ _ _ _ q hq with rfl | rfl | rfl | rfl <;> assumption
  have inner : wires (innerMid k (chainLast (chainLast L.control (ptXB L)) (ptYB L)) tk tc) ⊆ S := by
    intro q hq
    simp only [innerMid, wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, or_false] at hq
    rcases hq with (rfl | rfl | rfl) | rfl | rfl <;> assumption
  simp only [sharedPoint, sharedBlock, wires_append]
  refine Finset.union_subset (Finset.union_subset (Finset.union_subset (Finset.union_subset
    (xsub _ hXw _) (xsub _ hYw _)) (zsub _ _ _ chX ?_)) (xsub _ hYw _)) (xsub _ hXw _)
  rw [wires_append]
  exact Finset.union_subset pre (zsub _ _ _ chY inner)

theorem sharedPoint_physical (hn : L.wires.Nodup) (k tk tc : Wire) (hf : [k, tk, tc].Nodup)
    (hmem : ∀ q ∈ [k, tk, tc], q ∈ L.inPlaceFlags) (cx cy : Fp) (kSplit cSplit : Bool) :
    GatePhysical (sharedPoint L k tk tc cx cy kSplit cSplit) := by
  have names := sharedPoint_names L hw hn k tk tc hf hmem
  have nd := names.nodup
  have n1 := List.nodup_cons.mp nd
  have n2 := List.nodup_cons.mp n1.2
  have n3 := List.nodup_cons.mp n2.2
  have ndXY := n3.2
  have ndX : (chainWires L.control (ptXB L)).Nodup := (List.nodup_append.mp ndXY).1
  have ndY0 : ((ptYB L).flatMap ZeroBit.wires).Nodup := (List.nodup_append.mp ndXY).2.1
  have disXY := (List.nodup_append.mp ndXY).2.2
  have heX := chainLast_mem L.control (ptXB L)
  have heY : chainLast L.control (ptXB L) ∉ (ptYB L).flatMap ZeroBit.wires :=
    fun h => disXY _ heX _ h rfl
  have ndY : (chainWires (chainLast L.control (ptXB L)) (ptYB L)).Nodup :=
    List.nodup_cons.mpr ⟨heY, ndY0⟩
  have huY := chainLast_mem (chainLast L.control (ptXB L)) (ptYB L)
  have mem1 : ∀ q, q ∈ chainWires L.control (ptXB L) ++ (ptYB L).flatMap ZeroBit.wires →
      q ∈ tk :: tc :: (chainWires L.control (ptXB L) ++ (ptYB L).flatMap ZeroBit.wires) :=
    fun q h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
  have hYsub : ∀ q ∈ chainWires (chainLast L.control (ptXB L)) (ptYB L),
      q ∈ chainWires L.control (ptXB L) ++ (ptYB L).flatMap ZeroBit.wires := by
    intro q hq
    simp only [chainWires, List.mem_cons] at hq
    rcases hq with h | h
    · exact List.mem_append_left _ (h ▸ heX)
    · exact List.mem_append_right _ h
  have hktk : k ≠ tk := fun h => n1.1 (h ▸ List.mem_cons_self ..)
  have hktc : k ≠ tc := fun h => n1.1 (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have htc : tk ≠ tc := fun h => n2.1 (h ▸ List.mem_cons_self ..)
  have het : chainLast L.control (ptXB L) ≠ tk :=
    fun h => n2.1 (List.mem_cons_of_mem _ (List.mem_append_left _ (h ▸ heX)))
  have hec : chainLast L.control (ptXB L) ≠ tc :=
    fun h => n3.1 (List.mem_append_left _ (h ▸ heX))
  have hut : chainLast (chainLast L.control (ptXB L)) (ptYB L) ≠ tk :=
    fun h => n2.1 (List.mem_cons_of_mem _ (h ▸ hYsub _ huY))
  have huc : chainLast (chainLast L.control (ptXB L)) (ptYB L) ≠ tc :=
    fun h => n3.1 (h ▸ hYsub _ huY)
  have pre := preMid_physical k (chainLast L.control (ptXB L)) tk tc kSplit cSplit hec hktk het
  have inner : GatePhysical (innerMid k (chainLast (chainLast L.control (ptXB L)) (ptYB L)) tk tc) := by
    intro i hi
    simp only [innerMid, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hktk, hut⟩
    · exact huc
  simp only [sharedPoint, sharedBlock, gatePhysical_append]
  exact ⟨⟨⟨⟨xorConstant_physical _ _, xorConstant_physical _ _⟩,
    zeroWith_physical _ (by
      rw [gatePhysical_append]
      exact ⟨pre, zeroWith_physical _ inner _ _ ndY⟩) _ _ ndX⟩,
    xorConstant_physical _ _⟩, xorConstant_physical _ _⟩

theorem sharedPoint_gateSlots_le (k tk tc : Wire) (cx cy : Fp) (kSplit cSplit : Bool) :
    Challenge.gateSlots (sharedPoint L k tk tc cx cy kSplit cSplit) ≤ 6000 := by
  have ox := ptXB_length L hw
  have oy := ptYB_length L hw
  have a1 := Baselines.xorConstant_gateSlots_le ((ptXB L).map ZeroBit.input) (1 + 2 * cx.val)
  have a2 := Baselines.xorConstant_gateSlots_le ((ptYB L).map ZeroBit.input) cy.val
  have pm : Challenge.gateSlots (preMid k (chainLast L.control (ptXB L)) tk tc kSplit cSplit) ≤ 2 := by
    cases kSplit <;> cases cSplit <;> simp [preMid, Challenge.gateSlots, Challenge.instructionSlots]
  have im : Challenge.gateSlots (innerMid k (chainLast (chainLast L.control (ptXB L)) (ptYB L)) tk tc) = 2 := rfl
  simp only [List.length_map] at a1 a2
  simp only [sharedPoint, sharedBlock, Challenge.gateSlots_append, zeroWith_gateSlots, im, ox, oy]
  omega

end

/-! Flag-level steps. -/
section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hw hn in
theorem writeBit_flags_congr (G F : BasisState) (hq : ∀ q ∈ L.inPlaceFlags, G q = F q) (t : Wire) (v : Bool) :
    ∀ q ∈ L.inPlaceFlags, writeBit G t v q = writeBit F t v q := by
  intro q hq'
  by_cases h : q = t
  · subst q; simp [writeBit]
  · simp [writeBit, h, hq q hq']

theorem sharedIn_flags (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (b O D I G E H K : Bool) (hKb : K = true → b = true) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (sharedPoint L L.core.double L.doubleSelect L.genericSelect cx cy false (decide (cy ≠ -cy)))
      (PointDialogBoundary L R b (dialogFlagState L O (D ^^ (K && pointEqual R (.some hc)))
        (I ^^ (b && pointEqual R (-(.some hc)))) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hf : [L.core.double, L.doubleSelect, L.genericSelect].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or]; tauto
  have hmem : ∀ q ∈ [L.core.double, L.doubleSelect, L.genericSelect], q ∈ L.inPlaceFlags := by
    intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp [inPlaceFlags]
  have hh := sharedPoint_boundary L hw hn R b (dialogFlagState L O D I G E H K) _ _ _ hf hmem cx cy
    false (decide (cy ≠ -cy))
  have hr := dialogFlagState_read L hn O D I G E H K
  have m := shared_math R hc
  refine hh.conseq (fun _ h => h) (fun st h => h.congrFlags ?_)
  rw [hr.2.2.2.2.2.2]
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (D ^^ (K && pointEqual R (.some hc)))).2.1
  have u2 := (dialogFlagState_update L hn O (D ^^ (K && pointEqual R (.some hc))) I G E H K
    (I ^^ (b && pointEqual R (-(.some hc))))).2.2.1
  have hvk : (K && ((false && (b && (pointFinite R && decide (pointX R = cx.val)))) ^^
      ((b && (pointFinite R && decide (pointX R = cx.val))) && decide (pointY R = cy.val)))) =
      (K && pointEqual R (.some hc)) := by
    rw [m.1]; cases K <;> cases b <;> simp_all
  have hvc : ((decide (cy ≠ -cy) && (b && (pointFinite R && decide (pointX R = cx.val)))) ^^
      ((b && (pointFinite R && decide (pointX R = cx.val))) && decide (pointY R = cy.val))) =
      (b && pointEqual R (-(.some hc))) := by
    rw [m.2]; cases b <;> simp
  rw [hvk, hvc]
  unfold upd2
  rw [hr.2.1, hr.2.2.1]
  have hds : L.doubleSelect ≠ L.genericSelect := by tauto
  have step := writeBit_flags_congr L _ _ u1 L.genericSelect (I ^^ (b && pointEqual R (-(.some hc)))) q hq
  rw [step]
  exact u2 q hq

theorem sharedOut_flags (S : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (b O D I G E H K : Bool) (hEb : E = true → b = true) :
    Triple (PointDialogBoundary L S b (dialogFlagState L O D I G E H K))
      (sharedPoint L L.core.equalX L.core.equalNegY L.infinitySelect cx cy (decide (cy ≠ -cy)) false)
      (PointDialogBoundary L S b (dialogFlagState L (O ^^ (b && pointEqual S (.some hc))) D I G E
        (H ^^ (E && pointEqual S (-(.some hc)))) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hf : [L.core.equalX, L.core.equalNegY, L.infinitySelect].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or]; tauto
  have hmem : ∀ q ∈ [L.core.equalX, L.core.equalNegY, L.infinitySelect], q ∈ L.inPlaceFlags := by
    intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp [inPlaceFlags]
  have hh := sharedPoint_boundary L hw hn S b (dialogFlagState L O D I G E H K) _ _ _ hf hmem cx cy
    (decide (cy ≠ -cy)) false
  have hr := dialogFlagState_read L hn O D I G E H K
  have m := shared_math S hc
  refine hh.conseq (fun _ h => h) (fun st h => h.congrFlags ?_)
  rw [hr.2.2.2.2.1]
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (H ^^ (E && pointEqual S (-(.some hc))))).2.2.2.2.2.1
  have u2 := (dialogFlagState_update L hn O D I G E (H ^^ (E && pointEqual S (-(.some hc)))) K
    (O ^^ (b && pointEqual S (.some hc)))).1
  have hvk : (E && ((decide (cy ≠ -cy) && (b && (pointFinite S && decide (pointX S = cx.val)))) ^^
      ((b && (pointFinite S && decide (pointX S = cx.val))) && decide (pointY S = cy.val)))) =
      (E && pointEqual S (-(.some hc))) := by
    rw [m.2]; cases E <;> cases b <;> simp_all
  have hvc : ((false && (b && (pointFinite S && decide (pointX S = cx.val)))) ^^
      ((b && (pointFinite S && decide (pointX S = cx.val))) && decide (pointY S = cy.val))) =
      (b && pointEqual S (.some hc)) := by
    rw [m.1]; cases b <;> simp [Bool.and_assoc]
  rw [hvk, hvc]
  unfold upd2
  rw [hr.2.2.2.2.2.1, hr.1]
  have step := writeBit_flags_congr L _ _ u1 L.infinitySelect (O ^^ (b && pointEqual S (.some hc))) q hq
  rw [step]
  exact u2 q hq

end

end ECDSAAdd.Entrant
