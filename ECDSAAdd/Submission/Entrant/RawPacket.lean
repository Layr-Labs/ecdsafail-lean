import ECDSAAdd.Submission.Entrant.MainP1

/-!
# Fully decoded field packets

A regular field packet keeps three of its five trits encoded (`e3`) while the cells run, because
the codec's clean hole `s j 2` hosts the half window's carry `base 719`.  To reach the other trits
it pays two bridges (`d3 ++ midPerm ++ e3` and `d3short ++ swapTrit 0 4 ++ e3short`, 12 Toffolis).

The packets below host the carry on the retired carry `base 760` instead, so the hole is no longer
needed: the packet decodes all five trits once after opening (`d3`) and encodes them once before
closing (`e3`).  The bridges become pure trit permutations (`midPerm`, `swapTrit 0 4`, `midInv`).
The cells run on the same physical trit positions as in the regular packet.
-/

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588
open Arithmetic MappedCompressed Challenge RecordedQuantum Baselines
open MeasuredCodec5 (legalNat bitRun safe)

/-- Open a packet and decode all five trits. -/
def rawOpen : Program := stageOpen ++ d3
/-- Encode the three low trits and close the packet. -/
def rawClose : Program := e3 ++ stageClose
/-- Pure trit permutations between the raw stages. -/
def rawTransition (divide : Bool) (k : Nat) : Program :=
  if k=0 then (if divide then midPerm else swapTrit 0 4)
  else (if divide then swapTrit 0 4 else midInv)

theorem rawOpen_support : wires rawOpen⊆Finset.range 10 := by decide +kernel
theorem rawClose_support : wires rawClose⊆Finset.range 10 := by decide +kernel
theorem rawTransition_support (divide : Bool) (k : Nat) (hk : k<2) :
    wires (rawTransition divide k)⊆Finset.range 10 := by
  cases divide <;> interval_cases k <;> decide +kernel
theorem stagePermutation_support (divide : Bool) (k : Nat) (hk : k<3) :
    wires (stagePermutation divide k)⊆Finset.range 10 := by
  cases divide <;> interval_cases k <;> decide +kernel
theorem rawTransition_pure (divide : Bool) (k : Nat) (hk : k<2) :
    measurementCount (rawTransition divide k)=0 := by
  cases divide <;> interval_cases k <;> decide +kernel

private def rawActive (divide : Bool) (k x : Nat) : Bool :=
  (activeSlots divide k).all fun pair =>
    ((bitRun (stagePermutation divide k) x).testBit (2*pair.2)==x.testBit (2*pair.1)) &&
    ((bitRun (stagePermutation divide k) x).testBit (2*pair.2+1)==x.testBit (2*pair.1+1))

private theorem rawActive_true (divide : Bool) (k : Nat) (hk : k<3) (x : Nat) :
    rawActive divide k x=true := by
  have a := Replay.permA_view x
  have b := Replay.permB_view x
  have m := Replay.permMid_view x
  cases divide <;> interval_cases k <;>
    simp [rawActive,stagePermutation,activeSlots,a.1,a.2.1,a.2.2.1,a.2.2.2,
      b.1,b.2,m.1,m.2.1,m.2.2.1,m.2.2.2]

theorem rawStage_correct (divide : Bool) (k : Nat) (hk : k<3)
    (state : State) (records : List Bool) (legal : MeasuredCodec5.legal state.basis) :
    (run (stagePermutation divide k) records state).phase=state.phase ∧
    ∀logical physical,(logical,physical)∈activeSlots divide k →
      (run (stagePermutation divide k) records state).basis (2*physical)=state.basis (2*logical) ∧
      (run (stagePermutation divide k) records state).basis (2*physical+1)=state.basis (2*logical+1) := by
  obtain ⟨x,hx,lx,hb⟩ := MeasuredCodec5.local_word state legal
  have agree := pool_run_agrees (stagePermutation divide k) (Finset.range 10)
    (stagePermutation_support divide k hk) records state ⟨state.phase,MeasuredCodec5.bitsOf x⟩ rfl hb
  have modeled := MeasuredCodec5.run_sim (stagePermutation divide k) records state.phase x
  rw [MeasuredCodec5.sim_safe (stagePermutation divide k) x (stagePermutation_safe divide k hk x)] at modeled
  have modeledPhase := congrArg State.phase modeled
  have output (q : Nat) (hq : q<10) :
      (run (stagePermutation divide k) records state).basis q=
        (bitRun (stagePermutation divide k) x).testBit q :=
    (agree.2 q (Finset.mem_range.mpr hq)).trans (congrArg (fun s : State => s.basis q) modeled)
  refine ⟨agree.1.trans modeledPhase,?_⟩
  intro logical physical used
  have bounds := activeSlots_bound divide k hk (logical,physical) used
  have word := (List.all_eq_true.mp (rawActive_true divide k hk x)) (logical,physical) used
  have values :
      (bitRun (stagePermutation divide k) x).testBit (2*physical)=x.testBit (2*logical) ∧
      (bitRun (stagePermutation divide k) x).testBit (2*physical+1)=x.testBit (2*logical+1) := by
    simpa only [Bool.and_eq_true,beq_iff_eq] using word
  exact ⟨(output _ (by omega)).trans
      (values.1.trans (hb _ (Finset.mem_range.mpr (by omega))).symm),
    (output _ (by omega)).trans
      (values.2.trans (hb _ (Finset.mem_range.mpr (by omega))).symm)⟩

theorem rawOpen_run (divide : Bool) (state : State) (mE mO mS : List Bool)
    (legal : MeasuredCodec5.legal state.basis) :
    run rawOpen mO (run (codeEncode divide) mE state)=run (stagePermutation divide 0) mS state := by
  apply composition_eq (codeEncode divide) rawOpen (stagePermutation divide 0)
    (by simpa only [(code_support divide).1] using (Finset.Subset.refl (Finset.range 10)))
    rawOpen_support (stagePermutation_support divide 0 (by decide)) _ state mE mO mS legal
  intro x hx lx
  have before := finite_code_encode divide x hx lx
  have step := finite_stageOpen divide x hx lx
  have rawLegal := stagePermutation_legal divide 0 (by decide) x hx lx
  have codec := Replay.c3_facts _ (Replay.legal3_of_legalNat _ rawLegal)
  have opened : bitRun stageOpen (bitRun (codeEncode divide) x)=
      bitRun e3 (bitRun (stagePermutation divide 0) x) := by
    rw [step.2,stageCode_split,Replay.bitRun_append]
  refine ⟨before.1,?_,stagePermutation_safe divide 0 (by decide) x,?_⟩
  · rw [rawOpen,Replay.safe_append,step.1,opened,codec.2.2.1]
    rfl
  · rw [rawOpen,Replay.bitRun_append,opened,codec.2.2.2]

theorem rawTransition_run (divide : Bool) (k : Nat) (hk : k<2)
    (state : State) (mE mT mO : List Bool) (legal : MeasuredCodec5.legal state.basis) :
    run (rawTransition divide k) mT (run (stagePermutation divide k) mE state)=
      run (stagePermutation divide (k+1)) mO state := by
  apply composition_eq (stagePermutation divide k) (rawTransition divide k)
    (stagePermutation divide (k+1)) (stagePermutation_support divide k (by omega))
    (rawTransition_support divide k hk) (stagePermutation_support divide (k+1) (by omega)) _
    state mE mT mO legal
  intro x _ _
  refine ⟨stagePermutation_safe divide k (by omega) x,
    Replay.safe_of_no_measurements _ (rawTransition_pure divide k hk) _,
    stagePermutation_safe divide (k+1) (by omega) x,?_⟩
  cases divide
  · interval_cases k
    · have r := Replay.swap_B_to_mid x
      simpa [rawTransition,stagePermutation] using r
    · simp [rawTransition,stagePermutation,Replay.bitRun_append,Replay.mid_inverse]
  · interval_cases k
    · simp [rawTransition,stagePermutation,Replay.bitRun_append]
    · have r := Replay.swap_mid_to_B x
      simpa [rawTransition,stagePermutation] using r

theorem rawClose_run (divide : Bool) (state : State) (mE mC mO : List Bool)
    (legal : MeasuredCodec5.legal state.basis) :
    run rawClose mC (run (stagePermutation divide 2) mE state)=run (codeEncode (!divide)) mO state := by
  apply composition_eq (stagePermutation divide 2) rawClose (codeEncode (!divide))
    (stagePermutation_support divide 2 (by decide)) rawClose_support
    (by simpa only [(code_support (!divide)).1] using (Finset.Subset.refl (Finset.range 10)))
    _ state mE mC mO legal
  intro x hx lx
  have step := finite_stageClose divide x hx lx
  have after := finite_code_encode (!divide) x hx lx
  have rawLegal := stagePermutation_legal divide 2 (by decide) x hx lx
  have codec := Replay.c3_facts _ (Replay.legal3_of_legalNat _ rawLegal)
  have coded : bitRun (stageCode divide 2) x=bitRun e3 (bitRun (stagePermutation divide 2) x) := by
    rw [stageCode_split,Replay.bitRun_append]
  refine ⟨stagePermutation_safe divide 2 (by decide) x,?_,after.1,?_⟩
  · rw [rawClose,Replay.safe_append,codec.1,← coded,step.1]
    rfl
  · rw [rawClose,Replay.bitRun_append,← coded,step.2]

def rawStageCodeAt (divide : Bool) (k : Nat) (f : Fin 10→Wire) : Program :=
  renameProgram (MeasuredCodec5.label f) (stagePermutation divide k)

theorem rawStageCodeAt_correct (divide : Bool) (k : Nat) (hk : k<3)
    (f : Fin 10→Wire) (hf : Function.Injective f) (state : State) (records : List Bool)
    (legal : MeasuredCodec5.legalAt f state.basis) :
    (run (rawStageCodeAt divide k f) records state).phase=state.phase ∧
    ∀logical physical,(logical,physical)∈activeSlots divide k →
      (run (rawStageCodeAt divide k f) records state).basis (MeasuredCodec5.label f (2*physical))=
        state.basis (MeasuredCodec5.label f (2*logical)) ∧
      (run (rawStageCodeAt divide k f) records state).basis (MeasuredCodec5.label f (2*physical+1))=
        state.basis (MeasuredCodec5.label f (2*logical+1)) := by
  let raw : State := ⟨state.phase,fun q => state.basis (MeasuredCodec5.label f q)⟩
  have result := rawStage_correct divide k hk raw records legal
  have placed := run_rename_pool (MeasuredCodec5.label f) (Finset.range 10)
    (FirstNonzeroCodec.label_inj' f hf) (stagePermutation divide k)
    (stagePermutation_support divide k hk) records raw state rfl (fun _ _ => rfl)
  refine ⟨placed.1.trans result.1,?_⟩
  intro logical physical used
  have bounds := activeSlots_bound divide k hk (logical,physical) used
  have values := result.2 logical physical used
  exact ⟨(placed.2 (2*physical) (Finset.mem_range.mpr (by omega))).trans values.1,
    (placed.2 (2*physical+1) (Finset.mem_range.mpr (by omega))).trans values.2⟩

theorem rawOpenAt_run (divide : Bool) (f : Fin 10→Wire) (hf : Function.Injective f)
    (state : State) (mE mO mS : List Bool) (legal : MeasuredCodec5.legalAt f state.basis) :
    run (renameProgram (MeasuredCodec5.label f) rawOpen) mO
      (run (codeEncodeAt divide f) mE state)=run (rawStageCodeAt divide 0 f) mS state := by
  exact mapped_composition_eq f hf (codeEncode divide) rawOpen (stagePermutation divide 0)
    (by simpa only [(code_support divide).1] using (Finset.Subset.refl (Finset.range 10)))
    rawOpen_support (stagePermutation_support divide 0 (by decide))
    (fun raw a b c h => rawOpen_run divide raw a b c h) state mE mO mS legal

theorem rawTransitionAt_run (divide : Bool) (k : Nat) (hk : k<2)
    (f : Fin 10→Wire) (hf : Function.Injective f) (state : State) (mE mT mO : List Bool)
    (legal : MeasuredCodec5.legalAt f state.basis) :
    run (renameProgram (MeasuredCodec5.label f) (rawTransition divide k)) mT
      (run (rawStageCodeAt divide k f) mE state)=run (rawStageCodeAt divide (k+1) f) mO state := by
  exact mapped_composition_eq f hf (stagePermutation divide k) (rawTransition divide k)
    (stagePermutation divide (k+1)) (stagePermutation_support divide k (by omega))
    (rawTransition_support divide k hk) (stagePermutation_support divide (k+1) (by omega))
    (fun raw a b c h => rawTransition_run divide k hk raw a b c h) state mE mT mO legal

theorem rawCloseAt_run (divide : Bool) (f : Fin 10→Wire) (hf : Function.Injective f)
    (state : State) (mE mC mO : List Bool) (legal : MeasuredCodec5.legalAt f state.basis) :
    run (renameProgram (MeasuredCodec5.label f) rawClose) mC
      (run (rawStageCodeAt divide 2 f) mE state)=run (codeEncodeAt (!divide) f) mO state := by
  exact mapped_composition_eq f hf (stagePermutation divide 2) rawClose (codeEncode (!divide))
    (stagePermutation_support divide 2 (by decide)) rawClose_support
    (by simpa only [(code_support (!divide)).1] using (Finset.Subset.refl (Finset.range 10)))
    (fun raw a b c h => rawClose_run divide raw a b c h) state mE mC mO legal

theorem rawStageCodeAt_neutral (divide : Bool) (k : Nat) (hk : k<3) (f : Fin 10→Wire) :
    MeasuredCodec5.zeroNeutral (rawStageCodeAt divide k f)=true := by
  rw [rawStageCodeAt,zeroNeutral_rename]
  cases divide <;> interval_cases k <;> decide +kernel

theorem rawStageCodeAt_sub (divide : Bool) (k : Nat) (f : Fin 10→Wire) :
    wires (rawStageCodeAt divide k f)⊆wires (stageCodeAt divide k f) := by
  rw [rawStageCodeAt,stageCodeAt,renameProgram_support,renameProgram_support,stageCode_split,wires_append]
  exact Finset.image_subset_image Finset.subset_union_left

theorem rawStageCodeAt_free (divide : Bool) (j k : Nat) (hj : j<102) (hk : k<3)
    (q : Nat) (low : 510≤q) (gap : q<1028 ∨ 1538≤q) :
    base q∉wires (rawStageCodeAt divide k (History5.historyMap base (5*j))) :=
  fun used => stageCodeAt_free divide j k hj hk q low gap (rawStageCodeAt_sub divide k _ used)

theorem rawStageCodeAt_disjoint (divide : Bool) (j k : Nat) (hj : j<102) (hk : k<3)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) :
    Disjoint (wires (rawStageCodeAt divide k (History5.historyMap base (5*j))))
      ((balancedSharedPorts base (base 2409)).r++(balancedSharedPorts base (base 2409)).y).toFinset :=
  Finset.disjoint_of_subset_left (rawStageCodeAt_sub divide k _) (stageCodeAt_disjoint divide j k hj hk origin ctx)

end ECDSAAdd.Entrant.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

/-- The half window with its carry `base 719` hosted on the retired carry `base 760`. -/
def rawHalfWindow (P : Program) (j active : Nat) : Program :=
  ControlLoan1589.loanWindow (g j active) (base 2409) (packetCarry j)
    (renameProgram (Equiv.swap (base 719) (base 760)) P)

def rawCellWith (divide : Bool) (P : Program) (j active : Nat) : Program :=
  if divide then
    rawHalfWindow P j active ++ SW.selW (s j active) (base 2409) FrontierSW1591.swapBody
  else
    SW.selW (s j active) (base 2409) FrontierSW1591.swapBody ++ rawHalfWindow P j active

def rawCell (divide : Bool) (j active : Nat) : Program :=
  rawCellWith divide (P1Life.half (base 760) divide base (base 2409)) j active

/-- A field packet that decodes all five trits once: same cells and physical trit positions as
`basePacket`, the bridges replaced by pure trit permutations. -/
def rawBasePacket (divide : Bool) (j : Nat) : Program :=
  onPacket j rawOpen ++
    (if divide then
      rawCell true j 3 ++ rawCell true j 4 ++ onPacket j (rawTransition true 0) ++
      rawCell true j 4 ++ rawCell true j 3 ++ onPacket j (rawTransition true 1) ++
      rawCell true j 4
    else
      rawCell false j 4 ++ onPacket j (rawTransition false 0) ++
      rawCell false j 3 ++ rawCell false j 4 ++ onPacket j (rawTransition false 1) ++
      rawCell false j 4 ++ rawCell false j 3) ++
    onPacket j rawClose

def rawPacket (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (rawBasePacket divide j)

theorem host760_work : base 760∈Q6EndpointCell.workIds.map base :=
  List.mem_map.mpr ⟨760,by simp [Q6EndpointCell.workIds,List.mem_range'_1],rfl⟩

theorem host760_free (P : Program) (support : HalfSupport P) : base 760∉wires P :=
  fun used => (Finset.mem_erase.mp (support used)).1 rfl

theorem rawHalfWindow_selected_eq (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P) (j active : Nat)
    (hj : j<102) (ha : active<5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (rValue : regValue (balancedSharedPorts base (base 2409)).r state.basis=wordIn X)
    (yValue : regValue (balancedSharedPorts base (base 2409)).y state.basis=wordIn Y)
    (flagIn : state.basis (base 2409)=false) :
    run (rawHalfWindow P j active) records state=
      run (SW.selW (g j active) (base 2409) P) records state := by
  let copied := run [.CX (g j active) (base 2409)] [] state
  let original := P
  let fresh := P
  let rebound := renameProgram (Equiv.swap (base 719) (base 760)) fresh
  have holeFlag : base 760≠base 2409 := HostOB5.host_ne _ _ (by omega)
  have holeFree : base 760∉wires fresh := host760_free P support
  have holeIn : state.basis (base 760)=false := clean _ host760_work
  have copiedHole : copied.basis (base 760)=false := by
    simpa only [copied,run,writeBit,Function.update_of_ne holeFlag] using holeIn
  have copiedClean := copied_work_clean (g j active) state clean
  have copiedFrame := copied_self_frame (g j active) state
    (wordIn X) (wordIn Y) rValue yValue
  have freshEq (m : List Bool) : run fresh m copied=run original m copied := rfl
  have member719 : base 719∈Q6EndpointCell.workIds.map base :=
    List.mem_map.mpr ⟨719,by simp [Q6EndpointCell.workIds,List.mem_range'_1],rfl⟩
  have away719 := half_work_away _ member719
  have bodyEq : ∀m,run rebound m copied=run original m copied := by
    intro m
    have result := law copied.basis copiedClean X Y copied m copiedFrame
    have after : (run fresh m copied).basis (base 719)=false := by
      rw [freshEq m]
      exact (result.2.2.2 _ (by simpa only [Q6EndpointCell.ports_r] using away719.1)
        (by simpa only [Q6EndpointCell.ports_y] using away719.2)).trans (copiedClean _ member719)
    exact (NewFieldFrameOB5.rebind_swap_run _ _ _ copied m (copiedClean _ member719) copiedHole after
      ((run_preserves_outside _ m copied _ holeFree).trans copiedHole)).trans (freshEq m)
  have oldResult := law copied.basis copiedClean X Y copied records copiedFrame
  have carryMember := packetCarry_mem_work j hj
  have carryAway := half_work_away _ carryMember
  have keep : (run rebound records copied).basis (base 2409)=copied.basis (base 2409) := by
    rw [bodyEq]
    exact oldResult.2.2.2 _
      (by simpa only [Q6EndpointCell.ports_r] using half_flag_away.1)
      (by simpa only [Q6EndpointCell.ports_y] using half_flag_away.2)
  have carryOut : (run rebound records copied).basis (packetCarry j)=false := by
    rw [bodyEq]
    exact (oldResult.2.2.2 _
      (by simpa only [Q6EndpointCell.ports_r] using carryAway.1)
      (by simpa only [Q6EndpointCell.ports_y] using carryAway.2)).trans
        (copiedClean _ carryMember)
  have activeFree : g j active∉wires rebound := by
    change g j active∉wires (renameProgram (Equiv.swap (base 719) (base 760)) fresh)
    rw [renameProgram_support]
    intro used
    obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp used
    have fix : Equiv.swap (base 719) (base 760) (g j active)=g j active :=
      Equiv.swap_apply_of_ne_of_ne
        (HostOB5.host_ne _ _ (by omega)) (HostOB5.host_ne _ _ (by omega))
    have same := (Equiv.swap (base 719) (base 760)).injective (eq.trans fix.symm)
    have noG : g j active∉wires fresh := body_history_gap_free P support _ (Or.inl (by omega))
    apply noG
    rw [←same]
    exact hq
  have gf : g j active≠base 2409 := HostOB5.host_ne _ _ (by omega)
  have cg : packetCarry j≠g j active := HostOB5.host_ne _ _ (by omega)
  have cf : packetCarry j≠base 2409 := HostOB5.host_ne _ _ (by omega)
  have loan := ControlLoan1589.loanWindow_eq (g j active) (base 2409) (packetCarry j)
    rebound state records gf cg cf activeFree flagIn (clean _ carryMember) keep carryOut
  have loanEq : run (rawHalfWindow P j active) records state=
      run (SW.selW (g j active) (base 2409) rebound) records state := loan
  rw [loanEq]
  have headCount : measurementCount [.CX (g j active) (base 2409)]=0 := rfl
  simp only [SW.selW,List.append_assoc,run_append,headCount,List.take_zero,
    List.drop_zero,run_take]
  rw [show measurementCount rebound=measurementCount original from
    (renameProgram_counts (Equiv.swap (base 719) (base 760)) P).2]
  rw [show run rebound records (run [.CX (g j active) (base 2409)] [] state)=
    run original records (run [.CX (g j active) (base 2409)] [] state) from bodyEq records]

theorem rawHalfWindow_frame (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P)
    (j active : Nat) (hj : j<102) (ha : active<5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (enabled : state.basis (base 2400)=true) (flagIn : state.basis (base 2409)=false)
    (rValue : regValue fieldR state.basis=wordIn X) (yValue : regValue fieldY state.basis=wordIn Y) :
    (run (rawHalfWindow P j active) records state).phase=state.phase ∧
    PairFrame fieldR fieldY state.basis
      (wordOut (if divide then (X+(if state.basis (g j active) then Y else -Y))/2
        else 2*X+(if state.basis (g j active) then -Y else Y))) (wordOut Y)
      (run (rawHalfWindow P j active) records state).basis := by
  rw [rawHalfWindow_selected_eq P divide wordIn wordOut law support j active hj ha X Y
    state records clean rValue yValue flagIn]
  exact selected_half_frame P divide wordIn wordOut law support j active hj ha X Y
    state records clean enabled flagIn rValue yValue

theorem rawCellWith_frame (P : Program) (divide : Bool) (wordIn wordOut : Fp → Nat)
    (law : HalfLaw P divide wordIn wordOut) (support : HalfSupport P)
    (j active : Nat) (hj : j<102) (ha : active<5) (X Y : Fp)
    (state : State) (records : List Bool) (clean : Q6EndpointCell.Clean base state.basis)
    (enabled : state.basis (base 2400)=true) (flagIn : state.basis (base 2409)=false)
    (rValue : regValue fieldR state.basis=wordIn X) (yValue : regValue fieldY state.basis=wordIn Y) :
    (run (rawCellWith divide P j active) records state).phase=state.phase ∧
    PairFrame fieldR fieldY state.basis
      (wordOut (Q6EndpointCell.payload divide (state.basis (g j active)) (state.basis (s j active)) (X,Y)).1)
      (wordOut (Q6EndpointCell.payload divide (state.basis (g j active)) (state.basis (s j active)) (X,Y)).2)
      (run (rawCellWith divide P j active) records state).basis := by
  cases divide
  · let head := SW.selW (s j active) (base 2409) FrontierSW1591.swapBody
    let before := run head (records.take (measurementCount head)) state
    let A : Fp := if state.basis (s j active) then Y else X
    let B : Fp := if state.basis (s j active) then X else Y
    have swapped := selected_swap_frame wordIn j active hj ha X Y state
      (records.take (measurementCount head)) enabled flagIn rValue yValue
    have same (q : Nat) (hr : q<2056 ∨ 2312≤q) (hy : q<770 ∨ 1026≤q) :
        before.basis (base q)=state.basis (base q) := route_pair_numeric _ _ _ _ swapped.2 q hr hy
    have result := rawHalfWindow_frame P false wordIn wordOut law support j active hj ha A B before
      (records.drop (measurementCount head)) (route_pair_clean _ _ _ _ swapped.2 clean)
      ((same 2400 (by omega) (by omega)).trans enabled)
      ((same 2409 (by omega) (by omega)).trans flagIn) swapped.2.1 swapped.2.2.1
    have composed := route_pair_compose _ _ _ _ _ _ _ swapped.2 result.2
    have gSame : before.basis (g j active)=state.basis (g j active) := same _ (by omega) (by omega)
    simp only [rawCellWith,Bool.false_eq_true,if_false,run_append]
    refine ⟨result.1.trans swapped.1,?_⟩
    cases e : state.basis (s j active) <;>
      simpa only [Q6EndpointCell.payload,skywalkPayloadUncell,Bool.false_eq_true,if_false,
        if_true,A,B,gSame,e] using composed
  · let head := rawHalfWindow P j active
    let before := run head (records.take (measurementCount head)) state
    let A : Fp := (X+(if state.basis (g j active) then Y else -Y))/2
    have first := rawHalfWindow_frame P true wordIn wordOut law support j active hj ha X Y state
      (records.take (measurementCount head)) clean enabled flagIn rValue yValue
    have same (q : Nat) (hr : q<2056 ∨ 2312≤q) (hy : q<770 ∨ 1026≤q) :
        before.basis (base q)=state.basis (base q) := route_pair_numeric _ _ _ _ first.2 q hr hy
    have result := selected_swap_frame wordOut j active hj ha A Y before
      (records.drop (measurementCount head))
      ((same 2400 (by omega) (by omega)).trans enabled)
      ((same 2409 (by omega) (by omega)).trans flagIn) first.2.1 first.2.2.1
    have composed := route_pair_compose _ _ _ _ _ _ _ first.2 result.2
    have sSame : before.basis (s j active)=state.basis (s j active) := same _ (by omega) (by omega)
    rw [rawCellWith,if_pos rfl,run_append]
    refine ⟨result.1.trans first.1,?_⟩
    cases e : state.basis (s j active) <;>
      simpa only [Q6EndpointCell.payload,skywalkPayloadCell,if_true,A,sSame,e,
        Bool.false_eq_true,if_false] using composed

structure RawStageFacts (wordR wordY : Fp → Nat) (divide : Bool) (j k : Nat) (origin : BasisState)
    (X Y : Fp) (state : State) : Prop where
  clean : Q6EndpointCell.Clean base state.basis
  flag : state.basis (base 2409)=false
  enabled : state.basis (base 2400)=true
  rValue : regValue (balancedSharedPorts base (base 2409)).r state.basis=wordR X
  yValue : regValue (balancedSharedPorts base (base 2409)).y state.basis=wordY Y
  active : ∀logical physical,(logical,physical)∈activeSlots divide k →
    state.basis (g j physical)=origin (g j logical) ∧
    state.basis (s j physical)=origin (s j logical)

theorem raw_stage_frame_facts (wordR wordY : Fp → Nat) (divide : Bool) (j k : Nat) (hj : j<102) (hk : k<3)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (state : State)
    (input : CodeFrame wordR wordY (rawStageCodeAt divide k (History5.historyMap base (5*j))) origin X Y state) :
    RawStageFacts wordR wordY divide j k origin X Y state := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := input
  have domain := NewHistory5.frame_history_legal base (base 2409) ctx.hn (ctx.hp _ (by simp))
    102 (by decide) origin raw.basis _ _ ctx.legal rawFrame
  have correct := rawStageCodeAt_correct divide k hk (History5.historyMap base (5*j))
    (History5.historyMap_injective base base_pool_nodup (5*j) (by omega)) raw [] (domain j hj)
  have historySame (port : Fin 10) :
      raw.basis (History5.historyMap base (5*j) port)=origin (History5.historyMap base (5*j) port) :=
    rawFrame.2.2 _ (History5.history_words_away base (base 2409) ctx.hn (ctx.hp _ (by simp))
      (5*j) (by omega) port).1
      (History5.history_words_away base (base 2409) ctx.hn (ctx.hp _ (by simp))
        (5*j) (by omega) port).2
  have rawSame (q : Nat) (hq : q<10) :
      raw.basis (MeasuredCodec5.label (History5.historyMap base (5*j)) q)=
        origin (MeasuredCodec5.label (History5.historyMap base (5*j)) q) := by
    simpa only [MeasuredCodec5.label,dif_pos hq] using historySame ⟨q,hq⟩
  have dis := rawStageCodeAt_disjoint divide j k hj hk origin ctx
  have before (q : Wire) (off : q∉wires (rawStageCodeAt divide k (History5.historyMap base (5*j)))) :
      state.basis q=raw.basis q := by
    rw [encoded]
    exact run_preserves_outside _ [] raw q off
  have valuesR : regValue (balancedSharedPorts base (base 2409)).r state.basis=
      regValue (balancedSharedPorts base (base 2409)).r raw.basis := by
    apply regValue_congr
    intro q hq
    exact before q (fun used => Finset.disjoint_left.mp dis used
      (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl hq))))
  have valuesY : regValue (balancedSharedPorts base (base 2409)).y state.basis=
      regValue (balancedSharedPorts base (base 2409)).y raw.basis := by
    apply regValue_congr
    intro q hq
    exact before q (fun used => Finset.disjoint_left.mp dis used
      (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inr hq))))
  refine ⟨?_,?_,?_,valuesR.trans rawFrame.1,valuesY.trans rawFrame.2.1,?_⟩
  · have originalClean := Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity
    intro q used
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp used
    have index := hi
    simp only [Q6EndpointCell.workIds,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false] at index
    have off := half_work_away (base i) (List.mem_map.mpr ⟨i,hi,rfl⟩)
    exact (before _ (rawStageCodeAt_free divide j k hj hk i (by omega) (by omega))).trans
      ((rawFrame.2.2 _ off.1 off.2).trans
        (originalClean _ (List.mem_map.mpr ⟨i,hi,rfl⟩)))
  · exact (before _ (rawStageCodeAt_free divide j k hj hk 2409 (by omega) (by omega))).trans
      ((rawFrame.2.2 _ half_flag_away.1 half_flag_away.2).trans ctx.hg0)
  · have away : base 2400∉(balancedSharedPorts base (base 2409)).r ∧
        base 2400∉(balancedSharedPorts base (base 2409)).y := by
      rw [balancedSharedPorts_r,balancedSharedPorts_y]
      exact ⟨OwnPlusHost.not_block 2400 2056 256 (by omega),
        OwnPlusHost.not_block 2400 770 256 (by omega)⟩
    exact (before _ (rawStageCodeAt_free divide j k hj hk 2400 (by omega) (by omega))).trans
      ((rawFrame.2.2 _ away.1 away.2).trans enabled)
  · intro logical physical used
    have bound := activeSlots_bound divide k hk (logical,physical) used
    have active := correct.2 logical physical used
    have a := active.1.trans (rawSame (2*logical) (by omega))
    have b := active.2.trans (rawSame (2*logical+1) (by omega))
    rw [encoded]
    simpa only [route_packet_label_g j physical bound.2,route_packet_label_s j physical bound.2,
      route_packet_label_g j logical bound.1,route_packet_label_s j logical bound.1] using And.intro a b

theorem raw_open_frame (wordR wordY : Fp → Nat) (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (X Y : Fp)
    (state : State) (records : List Bool)
    (input : CodeFrame wordR wordY (codeEncodeAt divide (History5.historyMap base (5*j))) origin X Y state) :
    (run (onPacket j rawOpen) records state).phase=state.phase ∧
      CodeFrame wordR wordY (rawStageCodeAt divide 0 (History5.historyMap base (5*j))) origin X Y
        (run (onPacket j rawOpen) records state) := by
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  have legal := route_raw_current_legal wordR wordY j hj origin ctx X Y raw rawFrame
  have injective := History5.historyMap_injective base base_pool_nodup (5*j) (by omega)
  have actual : run (onPacket j rawOpen) records state=
      run (rawStageCodeAt divide 0 (History5.historyMap base (5*j))) [] raw := by
    rw [encoded]
    exact rawOpenAt_run divide _ injective raw [] records [] legal
  have phase := (congrArg State.phase actual).trans
    (rawStageCodeAt_correct divide 0 (by decide) _ injective raw [] legal).1
  exact ⟨phase.trans rawPhase,raw,phase.symm,rawFrame,actual⟩

theorem raw_transition_frame (wordR wordY : Fp → Nat) (divide : Bool) (j k : Nat) (hj : j<102) (hk : k<2)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (X Y : Fp)
    (state : State) (records : List Bool)
    (input : CodeFrame wordR wordY (rawStageCodeAt divide k (History5.historyMap base (5*j))) origin X Y state) :
    (run (onPacket j (rawTransition divide k)) records state).phase=state.phase ∧
      CodeFrame wordR wordY (rawStageCodeAt divide (k+1) (History5.historyMap base (5*j))) origin X Y
        (run (onPacket j (rawTransition divide k)) records state) := by
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  have legal := route_raw_current_legal wordR wordY j hj origin ctx X Y raw rawFrame
  have injective := History5.historyMap_injective base base_pool_nodup (5*j) (by omega)
  have actual : run (onPacket j (rawTransition divide k)) records state=
      run (rawStageCodeAt divide (k+1) (History5.historyMap base (5*j))) [] raw := by
    rw [encoded]
    exact rawTransitionAt_run divide k hk _ injective raw [] records [] legal
  have phase := (congrArg State.phase actual).trans
    (rawStageCodeAt_correct divide (k+1) (by omega) _ injective raw [] legal).1
  exact ⟨phase.trans rawPhase,raw,phase.symm,rawFrame,actual⟩

theorem raw_close_frame (wordR wordY : Fp → Nat) (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (X Y : Fp)
    (state : State) (records : List Bool)
    (input : CodeFrame wordR wordY (rawStageCodeAt divide 2 (History5.historyMap base (5*j))) origin X Y state) :
    (run (onPacket j rawClose) records state).phase=state.phase ∧
      CodeFrame wordR wordY (codeEncodeAt (!divide) (History5.historyMap base (5*j))) origin X Y
        (run (onPacket j rawClose) records state) := by
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  have legal := route_raw_current_legal wordR wordY j hj origin ctx X Y raw rawFrame
  have injective := History5.historyMap_injective base base_pool_nodup (5*j) (by omega)
  have actual : run (onPacket j rawClose) records state=
      run (codeEncodeAt (!divide) (History5.historyMap base (5*j))) [] raw := by
    rw [encoded]
    exact rawCloseAt_run divide _ injective raw [] records [] legal
  have phase := (congrArg State.phase actual).trans
    (codeEncodeAt_correct (!divide) _ injective raw [] legal).1
  exact ⟨phase.trans rawPhase,raw,phase.symm,rawFrame,actual⟩

theorem raw_cell_frame (divide : Bool) (j k logical physical : Nat)
    (hj : j<102) (hk : k<3) (used : (logical,physical)∈activeSlots divide k)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) (state : State) (records : List Bool)
    (input : CodeFrame P1Life.oddWord P1Life.oddWord (rawStageCodeAt divide k (History5.historyMap base (5*j))) origin X Y state) :
    let V := Q6EndpointCell.payload divide (origin (g j logical)) (origin (s j logical)) (X,Y)
    (run (rawCell divide j physical) records state).phase=state.phase ∧
      CodeFrame P1Life.oddWord P1Life.oddWord (rawStageCodeAt divide k (History5.historyMap base (5*j))) origin V.1 V.2
        (run (rawCell divide j physical) records state) := by
  have facts := raw_stage_frame_facts P1Life.oddWord P1Life.oddWord divide j k hj hk origin ctx enabled X Y state input
  have bounds := activeSlots_bound divide k hk (logical,physical) used
  have result := rawCellWith_frame _ divide _ _ (half_law divide) (half_support divide) j physical hj bounds.2 X Y state records
    facts.clean facts.enabled facts.flag facts.rValue facts.yValue
  have controls := facts.active logical physical used
  rw [controls.1,controls.2] at result
  refine ⟨result.1,?_⟩
  exact CodeFrame.arithmetic_step P1Life.oddWord P1Life.oddWord P1Life.oddWord P1Life.oddWord _ origin X Y _ _ state _
    (rawStageCodeAt_neutral divide k hk _) (rawStageCodeAt_disjoint divide j k hj hk origin ctx)
    input result.1 result.2

theorem rawBasePacket_frame (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt divide (History5.historyMap base (5*j))) origin X Y)
      (rawBasePacket divide j)
      (fun state => let V := regularPayload divide j origin (X,Y)
        CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt (!divide) (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (rawStageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (d : Bool) (V : Fp×Fp) : StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt d (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j rawOpen) (Frame d 0 V) := by
    intro state records input
    exact raw_open_frame P1Life.oddWord P1Life.oddWord d j hj origin ctx V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k<3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (rawCell d j physical)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact raw_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k<2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (rawTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact raw_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have closing (d : Bool) (V : Fp×Fp) : StateTriple (Frame d 2 V)
      (onPacket j rawClose)
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt (!d) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact raw_close_frame P1Life.oddWord P1Life.oddWord d j hj origin ctx V.1 V.2 state records input
  cases divide
  · let V1 := regularStep false j origin 4 (X,Y)
    let V2 := regularStep false j origin 3 V1
    let V3 := regularStep false j origin 2 V2
    let V4 := regularStep false j origin 1 V3
    let V5 := regularStep false j origin 0 V4
    have result := (opening false (X,Y)).seq
      ((step false 0 4 4 (by decide) (by decide) (X,Y)).seq
      ((transfer false 0 (by decide) V1).seq
      ((step false 1 3 3 (by decide) (by decide) V1).seq
      ((step false 1 2 4 (by decide) (by decide) V2).seq
      ((transfer false 1 (by decide) V3).seq
      ((step false 2 1 4 (by decide) (by decide) V3).seq
      ((step false 2 0 3 (by decide) (by decide) V4).seq (closing false V5))))))))
    simpa only [rawBasePacket,regularPayload,
      Bool.false_eq_true,if_false,if_true,List.append_assoc] using result
  · let V1 := regularStep true j origin 0 (X,Y)
    let V2 := regularStep true j origin 1 V1
    let V3 := regularStep true j origin 2 V2
    let V4 := regularStep true j origin 3 V3
    let V5 := regularStep true j origin 4 V4
    have result := (opening true (X,Y)).seq
      ((step true 0 0 3 (by decide) (by decide) (X,Y)).seq
      ((step true 0 1 4 (by decide) (by decide) V1).seq
      ((transfer true 0 (by decide) V2).seq
      ((step true 1 2 4 (by decide) (by decide) V2).seq
      ((step true 1 3 3 (by decide) (by decide) V3).seq
      ((transfer true 1 (by decide) V4).seq
      ((step true 2 4 4 (by decide) (by decide) V4).seq (closing true V5))))))))
    simpa only [rawBasePacket,regularPayload,
      if_true,if_false,List.append_assoc] using result

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires

theorem rawHalfWindow_read_support (P : Program) (support : HalfSupport P) (j active : Nat)
    (hj : j<102) (ha : active<5) :
    wires (rawHalfWindow P j active)⊆FrontierReplay1591.readSites (5*j) := by
  let W := FrontierReplay1591.readSites (5*j)
  let rebound := renameProgram (Equiv.swap (base 719) (base 760)) P
  have raw : wires P⊆W := (body_ids_support P support).trans (route_fieldIds_read j)
  have carry719 : base 719∈W := route_id_read j 719 (by
    simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false]
    omega)
  have host760 : base 760∈W := route_id_read j 760 (by
    simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false]
    omega)
  have carry : packetCarry j∈W := route_id_read j (516+2*j) (by
    simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false]
    omega)
  have source := (route_history_read j active ha).1
  have rebind : wires rebound⊆W := route_rename_swap_support P
    (base 719) (base 760) W raw carry719 host760
  have loanBody : (wires rebound).image (Equiv.swap (packetCarry j) (g j active))⊆W := by
    rw [←renameProgram_support]
    exact route_rename_swap_support rebound (packetCarry j) (g j active)
      W rebind carry source
  intro q used
  rcases Finset.mem_union.mp
      (ControlLoan1589.loanWindow_support (g j active) (base 2409) (packetCarry j) rebound used)
      with edge|body
  · simp only [Finset.mem_insert,Finset.mem_singleton] at edge
    rcases edge with rfl|rfl
    · exact source
    · exact route_flag_read j
  · exact loanBody body

theorem rawCell_read_support (divide : Bool) (j active : Nat) (hj : j<102) (ha : active<5) :
    wires (rawCell divide j active)⊆FrontierReplay1591.readSites (5*j) := by
  let W := FrontierReplay1591.readSites (5*j)
  have swap : wires FrontierSW1591.swapBody⊆W := by
    have old : wires FrontierSW1591.swapBody⊆
        wires (Q6EndpointCell.body true base (base 2409) (base 2409)) := by
      simp only [FrontierSW1591.swapBody,Q6EndpointCell.body,if_true,wires_append,
        Q6EndpointCell.ports_r,Q6EndpointCell.ports_y]
      exact Finset.subset_union_right
    exact old.trans (Q6EndpointCell.body_support true base (base 2409) (base 2409) W
      (route_fieldIds_read j) (route_flag_read j))
  have selected := route_selected_read_support (s j active) (base 2409) FrontierSW1591.swapBody W
    (route_history_read j active ha).2 (route_flag_read j) swap
  have half := rawHalfWindow_read_support _ (half_support divide) j active hj ha
  cases divide <;> simp only [rawCell,rawCellWith,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.union_subset_iff] at half ⊢
  · exact ⟨selected,half⟩
  · exact ⟨half,selected⟩

theorem rawBasePacket_readSites_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (rawBasePacket divide j)⊆FrontierReplay1591.readSites (5*j) := by
  have opening := onPacket_read_support j rawOpen rawOpen_support
  have closing := onPacket_read_support j rawClose rawClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_read_support j (rawTransition d k) (rawTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    rawCell_read_support d j active hj ha
  cases divide
  · simp only [rawBasePacket,Bool.false_eq_true,if_false,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨cellAt false 4 (by decide),transfer false 0 (by decide)⟩,
      cellAt false 3 (by decide)⟩,cellAt false 4 (by decide)⟩,transfer false 1 (by decide)⟩,
      cellAt false 4 (by decide)⟩,cellAt false 3 (by decide)⟩⟩,closing⟩
  · simp only [rawBasePacket,if_true,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨cellAt true 3 (by decide),cellAt true 4 (by decide)⟩,
      transfer true 0 (by decide)⟩,cellAt true 4 (by decide)⟩,cellAt true 3 (by decide)⟩,
      transfer true 1 (by decide)⟩,cellAt true 4 (by decide)⟩⟩,closing⟩

theorem rawBasePacket_read_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (rawBasePacket divide j)⊆NewHistory5.groupReadSites base (base 2400)
      (base 2409) (base 2410) (5*j) ∪ {base 2312} :=
  (rawBasePacket_readSites_support divide j hj).trans (FrontierReplay1591.readSites_sub (5*j))

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

theorem rawBasePacket_replay_frame (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt divide (History5.historyMap base (5*j))) origin X Y)
      (rawBasePacket divide j)
      (fun state => let V := directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt (!divide) (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  simpa only [regularPayload_eq divide j hj origin enabled] using
    rawBasePacket_frame divide j hj origin ctx enabled X Y

theorem rawBasePacket_cut_frame (divide : Bool) (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord (if divide then j else j+1) origin X Y) (rawBasePacket divide j)
      (fun state => let V := directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord (if divide then j+1 else j) origin V.1 V.2 state) := by
  have nonzero : j≠0 := by omega
  cases divide
  · intro state records input
    apply cut_window_frame P1Life.oddWord P1Life.oddWord P1Life.oddWord P1Life.oddWord (j+1) j j hj origin X Y _ _ (rawBasePacket false j)
      (otherEncodeCut_step base j 102).symm
      (otherEncodeCut_body_disjoint (j+1) j hj origin ctx _
        (rawBasePacket_read_support false j hj)) _ state records input
    intro current tape frame
    have normalized : CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt false (History5.historyMap base (5*j)))
        origin X Y current := by
      simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using
      rawBasePacket_replay_frame false j hj origin ctx enabled X Y current tape normalized
  · intro state records input
    apply cut_window_frame P1Life.oddWord P1Life.oddWord P1Life.oddWord P1Life.oddWord j (j+1) j hj origin X Y _ _ (rawBasePacket true j)
      (otherEncodeCut_step base j 102)
      (otherEncodeCut_body_disjoint j j hj origin ctx _
        (rawBasePacket_read_support true j hj)) _ state records input
    intro current tape frame
    have normalized : CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt true (History5.historyMap base (5*j)))
        origin X Y current := by
      simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using
      rawBasePacket_replay_frame true j hj origin ctx enabled X Y current tape normalized

/-- The fully decoded packet has the frame law of the regular packet (`packet_cut_frame`). -/
theorem rawPacket_cut_frame (divide : Bool) (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord (if divide then j else j+1) origin X Y) (rawPacket divide j)
      (fun state => let V := directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord (if divide then j+1 else j) origin V.1 V.2 state) := by
  intro state records input
  have raw := rawBasePacket_cut_frame divide j first hj origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi j) (rawBasePacket divide j)
    (fun q hq => Placement5.pi_outside j q hj hq) state records
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx X Y state input)
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx _ _ _ raw.2)
  change run (rawPacket divide j) records state=run (rawBasePacket divide j) records state at same
  rw [same]
  exact raw

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed
open ECDSAAdd.Entrant.Rolling1588

theorem rawCellWith_measure (c : Stair44Resources.Cost) (divide : Bool) (P : Program) (j active hole : Nat) :
    c.measure (rawCellWith divide P j active)=c.measure (cellWith divide P j active hole) := by
  cases divide <;> simp only [rawCellWith,cellWith,rawHalfWindow,halfWindowWith,ControlLoan1589.loanWindow,
    c.append,c.rename,if_true,if_false,Bool.false_eq_true]

theorem rawCell_measure (c : Stair44Resources.Cost) (divide : Bool) (j active hole : Nat) :
    c.measure (rawCell divide j active)=c.measure (cell divide j active hole) := by
  have shape : cell divide j active hole=cellWith divide (P1Life.half (base 760) divide base (base 2409)) j active hole := by
    cases divide <;> rfl
  rw [shape]
  exact rawCellWith_measure c divide _ j active hole

/-- Every cost of a fully decoded packet is that of the regular packet minus the shortened
codec pair `d3short`/`e3short`. -/
theorem rawPacket_measure (c : Stair44Resources.Cost) (divide : Bool) (j : Nat) (regular : divide=true → j≠84) :
    c.measure (rawPacket divide j)+c.measure d3short+c.measure e3short=c.measure (packet divide j) := by
  have h3 := rawCell_measure c divide j 3 2
  have h4 := rawCell_measure c divide j 4 2
  cases divide
  · simp only [rawPacket,packet,c.rename,rawBasePacket,basePacket,onPacket,c.append,rawOpen,rawClose,
      rawTransition,bridge5,bridge7inv,stageOpen,stageClose,if_true,if_false,Bool.false_eq_true,
      show ¬(1:Nat)=0 from by decide] at h3 h4 ⊢
    omega
  · have nonterminal : j≠84 := regular rfl
    simp only [rawPacket,packet,c.rename,rawBasePacket,basePacket,onPacket,c.append,rawOpen,rawClose,
      rawTransition,bridge7,bridge5,stageOpen,stageClose,if_true,if_false,if_neg nonterminal,
      show ¬(1:Nat)=0 from by decide] at h3 h4 ⊢
    omega

theorem codec_short_counts :
    toffoliCount d3short+toffoliCount e3short=5 ∧ measurementCount d3short+measurementCount e3short=1 ∧
      Challenge.gateSlots d3short+Challenge.gateSlots e3short=223 := by
  decide +kernel

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires

/-- `basePacket` without the terminal `dend` cell of the division packet 84 (all five cells regular). -/
def regularBasePacket (divide : Bool) (j : Nat) : Program :=
  onPacket j (dp ++ ParityCodec5New.untwist) ++
    (if divide then
      cell true j 3 2 ++ cell true j 4 2 ++ onPacket j bridge7 ++
      cell true j 4 2 ++ cell true j 3 2 ++ onPacket j bridge5 ++
      cell true j 4 2
    else
      cell false j 4 2 ++ onPacket j bridge5 ++
      cell false j 3 2 ++ cell false j 4 2 ++ onPacket j bridge7inv ++
      cell false j 4 2 ++ cell false j 3 2) ++
    onPacket j (ParityCodec5New.twist ++ ep)

theorem basePacket_regular (divide : Bool) (j : Nat) (regular : divide=true → j≠84) :
    basePacket divide j=regularBasePacket divide j := by
  cases divide
  · simp only [basePacket,regularBasePacket,Bool.false_eq_true,if_false]
  · simp only [basePacket,regularBasePacket,if_true,if_neg (regular rfl)]

theorem rawPacket_measure_regular (c : Stair44Resources.Cost) (divide : Bool) (j : Nat) :
    c.measure (rawPacket divide j)+c.measure d3short+c.measure e3short=
      c.measure (regularBasePacket divide j) := by
  have h3 := rawCell_measure c divide j 3 2
  have h4 := rawCell_measure c divide j 4 2
  cases divide
  · simp only [rawPacket,c.rename,rawBasePacket,regularBasePacket,onPacket,c.append,rawOpen,rawClose,
      rawTransition,bridge5,bridge7inv,stageOpen,stageClose,if_true,if_false,Bool.false_eq_true,
      show ¬(1:Nat)=0 from by decide] at h3 h4 ⊢
    omega
  · simp only [rawPacket,c.rename,rawBasePacket,regularBasePacket,onPacket,c.append,rawOpen,rawClose,
      rawTransition,bridge7,bridge5,stageOpen,stageClose,if_true,if_false,
      show ¬(1:Nat)=0 from by decide] at h3 h4 ⊢
    omega

theorem loanWindow_wires_mono (g f c h : Wire) (X Y : Program)
    (sub : (wires X).image (Equiv.swap c g)⊆insert h ((wires Y).image (Equiv.swap c g))) :
    wires (ControlLoan1589.loanWindow g f c X)⊆insert h (wires (ControlLoan1589.loanWindow g f c Y)) := by
  intro q hq
  simp only [ControlLoan1589.loanWindow,wires_append,renameProgram_support,Finset.mem_union] at hq ⊢
  rcases hq with (h1|h2)|h3
  · exact Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h1))))
  · rcases Finset.mem_insert.mp (sub h2) with e|m
    · exact Finset.mem_insert.mpr (Or.inl e)
    · exact Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr m))))
  · exact Finset.mem_insert_of_mem (Finset.mem_union.mpr (Or.inr h3))

theorem rawHalfWindow_wires (P : Program) (support : HalfSupport P) (j active : Nat)
    (hj : j<102) (ha : active<5) :
    wires (rawHalfWindow P j active)⊆insert (base 760) (wires (halfWindowWith P j active 2)) := by
  apply loanWindow_wires_mono
  intro q hq
  rw [renameProgram_support,Finset.image_image] at hq
  rw [renameProgram_support,Finset.image_image]
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  have c760 : packetCarry j≠base 760 := HostOB5.host_ne _ _ (by omega)
  have g760 : g j active≠base 760 := HostOB5.host_ne _ _ (by omega)
  by_cases e : p=base 719
  · subst e
    apply Finset.mem_insert.mpr
    left
    simp only [Function.comp_apply,Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne c760.symm g760.symm
  · have p760 : p≠base 760 := fun h => host760_free P support (h ▸ hp)
    have pHole : p≠s j 2 := by
      intro h
      apply body_history_free P support (1028+5*j+2) (Or.inr ⟨by omega,by omega⟩)
      rw [show base (1028+5*j+2)=s j 2 from rfl,← h]
      exact hp
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨p,hp,?_⟩
    simp only [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne e p760,
      Equiv.swap_apply_of_ne_of_ne e pHole]

theorem rawCell_wires (divide : Bool) (j active : Nat) (hj : j<102) (ha : active<5) :
    wires (rawCell divide j active)⊆insert (base 760) (wires (cell divide j active 2)) := by
  have shape : cell divide j active 2=cellWith divide (P1Life.half (base 760) divide base (base 2409)) j active 2 := by
    cases divide <;> rfl
  rw [shape]
  have half := rawHalfWindow_wires _ (half_support divide) j active hj ha
  intro q hq
  cases divide <;> simp only [rawCell,rawCellWith,cellWith,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union] at hq ⊢
  · rcases hq with h1|h2
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h1)
    · rcases Finset.mem_insert.mp (half h2) with e|m
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ m)
  · rcases hq with h1|h2
    · rcases Finset.mem_insert.mp (half h1) with e|m
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ m)
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h2)

theorem onPacket_wires_mono (j : Nat) (P Q R : Program) (sub : wires P⊆wires Q∪wires R) :
    wires (onPacket j P)⊆wires (onPacket j Q)∪wires (onPacket j R) := by
  simp only [onPacket,renameProgram_support,← Finset.image_union]
  exact Finset.image_subset_image sub

theorem rawOpen_wires (divide : Bool) :
    wires rawOpen⊆wires (dp++ParityCodec5New.untwist)∪wires (if divide then bridge7 else bridge7inv) := by
  cases divide <;> decide +kernel
theorem rawClose_wires (divide : Bool) :
    wires rawClose⊆wires (ParityCodec5New.twist++ep)∪wires (if divide then bridge7 else bridge7inv) := by
  cases divide <;> decide +kernel
theorem rawBasePacket_wires (divide : Bool) (j : Nat) (hj : j<102) :
    wires (rawBasePacket divide j)⊆insert (base 760) (wires (regularBasePacket divide j)) := by
  have c3 := rawCell_wires divide j 3 hj (by decide)
  have c4 := rawCell_wires divide j 4 hj (by decide)
  have o := onPacket_wires_mono j _ _ _ (rawOpen_wires divide)
  have cl := onPacket_wires_mono j _ _ _ (rawClose_wires divide)
  have pure (P Q : Program) (h : wires P⊆wires Q) : wires (onPacket j P)⊆wires (onPacket j Q) := by
    simp only [onPacket,renameProgram_support]
    exact Finset.image_subset_image h
  cases divide
  · have t0 := pure (rawTransition false 0) bridge5 (by decide +kernel)
    have t1 := pure (rawTransition false 1) bridge7inv (by decide +kernel)
    simp only [Bool.false_eq_true,if_false] at o cl
    simp only [rawBasePacket,regularBasePacket,wires_append,Bool.false_eq_true,if_false]
    generalize wires (onPacket j rawOpen)=A0 at *
    generalize wires (onPacket j rawClose)=A1 at *
    generalize wires (onPacket j (rawTransition false 0))=A2 at *
    generalize wires (onPacket j (rawTransition false 1))=A3 at *
    generalize wires (rawCell false j 3)=A4 at *
    generalize wires (rawCell false j 4)=A5 at *
    generalize wires (onPacket j (dp++ParityCodec5New.untwist))=B0 at *
    generalize wires (onPacket j (ParityCodec5New.twist++ep))=B1 at *
    generalize wires (onPacket j bridge5)=B2 at *
    generalize wires (onPacket j bridge7inv)=B3 at *
    generalize wires (cell false j 3 2)=B4 at *
    generalize wires (cell false j 4 2)=B5 at *
    intro q hq
    have h0 := @o q
    have h1 := @cl q
    have h2 := @t0 q
    have h3 := @t1 q
    have h4 := @c3 q
    have h5 := @c4 q
    simp only [Finset.mem_union,Finset.mem_insert] at hq h0 h1 h2 h3 h4 h5 ⊢
    rcases hq with ((h|((((((h|h)|h)|h)|h)|h)|h))|h)
    all_goals first
      | exact (h0 h).elim (fun x => by simp only [x,true_or,or_true]) (fun x => by simp only [x,true_or,or_true])
      | exact (h1 h).elim (fun x => by simp only [x,true_or,or_true]) (fun x => by simp only [x,true_or,or_true])
      | exact (by simp only [h2 h,true_or,or_true])
      | exact (by simp only [h3 h,true_or,or_true])
      | exact (h4 h).elim (fun x => Or.inl x) (fun x => by simp only [x,true_or,or_true])
      | exact (h5 h).elim (fun x => Or.inl x) (fun x => by simp only [x,true_or,or_true])
  · have t0 := pure (rawTransition true 0) bridge7 (by decide +kernel)
    have t1 := pure (rawTransition true 1) bridge5 (by decide +kernel)
    simp only [if_true] at o cl
    simp only [rawBasePacket,regularBasePacket,wires_append,if_true]
    generalize wires (onPacket j rawOpen)=A0 at *
    generalize wires (onPacket j rawClose)=A1 at *
    generalize wires (onPacket j (rawTransition true 0))=A2 at *
    generalize wires (onPacket j (rawTransition true 1))=A3 at *
    generalize wires (rawCell true j 3)=A4 at *
    generalize wires (rawCell true j 4)=A5 at *
    generalize wires (onPacket j (dp++ParityCodec5New.untwist))=B0 at *
    generalize wires (onPacket j (ParityCodec5New.twist++ep))=B1 at *
    generalize wires (onPacket j bridge5)=B2 at *
    generalize wires (onPacket j bridge7)=B3 at *
    generalize wires (cell true j 3 2)=B4 at *
    generalize wires (cell true j 4 2)=B5 at *
    intro q hq
    have h0 := @o q
    have h1 := @cl q
    have h2 := @t0 q
    have h3 := @t1 q
    have h4 := @c3 q
    have h5 := @c4 q
    simp only [Finset.mem_union,Finset.mem_insert] at hq h0 h1 h2 h3 h4 h5 ⊢
    rcases hq with ((h|((((((h|h)|h)|h)|h)|h)|h))|h)
    all_goals first
      | exact (h0 h).elim (fun x => by simp only [x,true_or,or_true]) (fun x => by simp only [x,true_or,or_true])
      | exact (h1 h).elim (fun x => by simp only [x,true_or,or_true]) (fun x => by simp only [x,true_or,or_true])
      | exact (by simp only [h2 h,true_or,or_true])
      | exact (by simp only [h3 h,true_or,or_true])
      | exact (h4 h).elim (fun x => Or.inl x) (fun x => by simp only [x,true_or,or_true])
      | exact (h5 h).elim (fun x => Or.inl x) (fun x => by simp only [x,true_or,or_true])

theorem shifted_fixes_760 (j : Nat) (hj : j<102) : shifted (Placement5.pi j) (base 760)=base 760 := by
  rw [shifted_base,Placement5.pi_outside j 760 hj (by
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion; omega)]

theorem rawPacket_wires (divide : Bool) (j : Nat) (hj : j<102) :
    wires (rawPacket divide j)⊆insert (base 760)
      (wires (renameProgram (shifted (Placement5.pi j)) (regularBasePacket divide j))) := by
  intro q hq
  rw [rawPacket,renameProgram_support] at hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (rawBasePacket_wires divide j hj hp) with e|m
  · subst e
    apply Finset.mem_insert.mpr
    left
    exact shifted_fixes_760 j hj
  · exact Finset.mem_insert_of_mem (by rw [renameProgram_support]; exact Finset.mem_image_of_mem _ m)

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires

/-! The regular packets never touch the retired carry `base 760` (so the fully decoded packets
may host their carry there). -/

private theorem r760_rename_free (f : Wire→Wire) (hf : Function.Injective f)
    (P : Program) (a b : Wire) (mapped : f a=b) (free : a∉wires P) :
    b∉wires (renameProgram f P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp used
  exact free (hf (eq.trans mapped.symm) ▸ hq)

private theorem r760_selected_free (source flag q : Wire) (P : Program)
    (sourceAway : q≠source) (flagAway : q≠flag) (free : q∉wires P) :
    q∉wires (SW.selW source flag P) := by
  simpa [SW.selW,wires_append,wires,Instr.wires,correctionWires,
    sourceAway,flagAway] using free

private theorem r760_swap_free : base 760∉wires FrontierSW1591.swapBody := by
  intro used
  have member := swapRegisters_wires (base 2409) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y
    (by simp [balancedSharedPorts_r,balancedSharedPorts_y,wireBlock]) used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,balancedSharedPorts_r,
    balancedSharedPorts_y,wireBlock,List.mem_map,List.mem_range'_1,base_injective.eq_iff] at member
  omega

private theorem r760_halfWindow_free (divide : Bool) (j active : Nat)
    (hj : j<102) (ha : active<5) : base 760∉wires (halfWindow divide j active 2) := by
  let P := P1Life.half (base 760) divide base (base 2409)
  let rebound := renameProgram (Equiv.swap (base 719) (s j 2)) P
  have fixHole : Equiv.swap (base 719) (s j 2) (base 760)=base 760 :=
    Equiv.swap_apply_of_ne_of_ne (HostOB5.host_ne _ _ (by omega)) (HostOB5.host_ne _ _ (by omega))
  have no760 : base 760∉wires rebound :=
    r760_rename_free _ (Equiv.swap (base 719) (s j 2)).injective P (base 760) (base 760)
      fixHole (host760_free P (half_support divide))
  have awayG : base 760≠g j active := HostOB5.host_ne _ _ (by omega)
  have awayC : base 760≠packetCarry j := HostOB5.host_ne _ _ (by omega)
  have fixed : Equiv.swap (packetCarry j) (g j active) (base 760)=base 760 :=
    Equiv.swap_apply_of_ne_of_ne awayC awayG
  have mid := r760_rename_free _ (Equiv.swap (packetCarry j) (g j active)).injective rebound
    (base 760) (base 760) fixed no760
  intro used
  rcases Finset.mem_union.mp
      (ControlLoan1589.loanWindow_support (g j active) (base 2409) (packetCarry j) rebound used)
      with edge|body
  · simp only [Finset.mem_insert,Finset.mem_singleton] at edge
    exact edge.elim awayG (by decide)
  · exact mid (by simpa only [renameProgram_support] using body)

private theorem r760_cell_free (divide : Bool) (j active : Nat)
    (hj : j<102) (ha : active<5) : base 760∉wires (cell divide j active 2) := by
  have half := r760_halfWindow_free divide j active hj ha
  have swap := r760_selected_free (s j active) (base 2409) (base 760) FrontierSW1591.swapBody
    (HostOB5.host_ne _ _ (by omega)) (by decide) r760_swap_free
  cases divide <;> simp only [cell,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.mem_union,not_or]
  · exact ⟨swap,half⟩
  · exact ⟨half,swap⟩

private theorem r760_onPacket_free (j : Nat) (hj : j<102) (P : Program)
    (support : wires P⊆Finset.range 10) : base 760∉wires (onPacket j P) := by
  rw [onPacket,renameProgram_support]
  intro used
  obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp used
  have bound := Finset.mem_range.mp (support hi)
  have site : MeasuredCodec5.label (History5.historyMap base (5*j)) i=
      History5.historyMap base (5*j) ⟨i,bound⟩ := by
    simp only [MeasuredCodec5.label,dif_pos bound]
  rw [site] at eq
  have same := base_injective (eq.trans (rfl : base 760=base 760))
  unfold History5.historyId at same
  split_ifs at same <;> omega

theorem regularBasePacket_760_free (divide : Bool) (j : Nat) (hj : j<102) :
    base 760∉wires (regularBasePacket divide j) := by
  have opening := r760_onPacket_free j hj (dp++ParityCodec5New.untwist) stageOpen_support
  have closing := r760_onPacket_free j hj (ParityCodec5New.twist++ep) stageClose_support
  have b7 := r760_onPacket_free j hj bridge7 (stageTransition_support true 0 (by decide))
  have b5 := r760_onPacket_free j hj bridge5 (stageTransition_support true 1 (by decide))
  have b7i := r760_onPacket_free j hj bridge7inv (stageTransition_support false 1 (by decide))
  have cellAt (k : Nat) (hk : k<5) := r760_cell_free divide j k hj hk
  cases divide <;> simp only [regularBasePacket,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.mem_union,not_or]
  all_goals repeat' apply And.intro
  all_goals first
    | exact opening
    | exact closing
    | exact b7
    | exact b5
    | exact b7i
    | exact cellAt 3 (by decide)
    | exact cellAt 4 (by decide)

theorem regularPacket_760_free (divide : Bool) (j : Nat) (hj : j<102) :
    base 760∉wires (renameProgram (shifted (Placement5.pi j)) (regularBasePacket divide j)) :=
  r760_rename_free _ (shifted (Placement5.pi j)).injective _ _ _
    (shifted_fixes_760 j hj) (regularBasePacket_760_free divide j hj)

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
open ECDSAAdd.Entrant.Rolling1588

theorem rawHalfWindow_physical (P : Program) (hp : GatePhysical P)
    (j active : Nat) (hj : j<102) (ha : active<5) : GatePhysical (rawHalfWindow P j active) := by
  apply ControlLoan1589.loanWindow_physical
  · exact HostOB5.host_ne _ _ (by omega)
  · exact gatePhysical_rename _ (Equiv.swap (base 719) (base 760)).injective _ hp

theorem rawCell_physical (divide : Bool) (j active : Nat) (hj : j<102) (ha : active<5) :
    GatePhysical (rawCell divide j active) := by
  have half := rawHalfWindow_physical _ (route_body_physical divide) j active hj ha
  have swap := route_selected_physical (s j active) (base 2409) FrontierSW1591.swapBody
    (HostOB5.host_ne _ _ (by omega)) route_swap_physical
  cases divide <;> simp only [rawCell,rawCellWith,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨swap,half⟩
  · exact ⟨half,swap⟩

theorem raw_codec_physical : GatePhysical rawOpen ∧ GatePhysical rawClose ∧
    ∀divide k,k<2→GatePhysical (rawTransition divide k) := by
  refine ⟨?_,?_,?_⟩
  · apply physicalGateCheck_correct
    decide +kernel
  · apply physicalGateCheck_correct
    decide +kernel
  · intro divide k hk
    apply physicalGateCheck_correct
    cases divide <;> interval_cases k <;> decide +kernel

theorem rawBasePacket_physical (divide : Bool) (j : Nat) (hj : j<102) :
    GatePhysical (rawBasePacket divide j) := by
  have opening := onPacket_physical j hj rawOpen rawOpen_support raw_codec_physical.1
  have closing := onPacket_physical j hj rawClose rawClose_support raw_codec_physical.2.1
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_physical j hj (rawTransition d k) (rawTransition_support d k hk)
      (raw_codec_physical.2.2 d k hk)
  have cellAt (k : Nat) (hk : k<5) := rawCell_physical divide j k hj hk
  cases divide <;> simp only [rawBasePacket,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  all_goals repeat' apply And.intro
  all_goals first
    | exact opening
    | exact closing
    | exact transfer false 0 (by decide)
    | exact transfer false 1 (by decide)
    | exact transfer true 0 (by decide)
    | exact transfer true 1 (by decide)
    | exact cellAt 3 (by decide)
    | exact cellAt 4 (by decide)

theorem rawPacket_physical (divide : Bool) (j : Nat) (hj : j<102) :
    GatePhysical (rawPacket divide j) :=
  gatePhysical_rename _ (shifted (Placement5.pi j)).injective _ (rawBasePacket_physical divide j hj)

/-- Renaming only reads the renaming on the program's own wires. -/
theorem renameProgram_congr_on (f g : Wire → Wire) (P : Program) (h : ∀q∈wires P,f q=g q) :
    renameProgram f P=renameProgram g P := by
  induction P with
  | nil => rfl
  | cons i P ih =>
    have tail : ∀q∈wires P,f q=g q := fun q hq => h q (by
      simp only [wires,Finset.mem_union]; exact Or.inr hq)
    have head : ∀q∈i.wires,f q=g q := fun q hq => h q (by
      simp only [wires,Finset.mem_union]; exact Or.inl hq)
    have rest := ih tail
    simp only [renameProgram,List.map_cons] at rest ⊢
    rw [rest]
    congr 1
    cases i with
    | X t => simp only [renameInstr,head t (by simp [Instr.wires])]
    | CX a b => simp only [renameInstr,head a (by simp [Instr.wires]),head b (by simp [Instr.wires])]
    | CCX a b c => simp only [renameInstr,head a (by simp [Instr.wires]),head b (by simp [Instr.wires]),
        head c (by simp [Instr.wires])]
    | measureX t c0 c1 =>
      have corr (cs : List Correction) (hc : ∀q∈correctionWires cs,f q=g q) :
          cs.map (renameCorrection f)=cs.map (renameCorrection g) := by
        induction cs with
        | nil => rfl
        | cons c cs ihc =>
          have hcs : ∀q∈correctionWires cs,f q=g q := fun q hq => hc q (by
            cases c <;> simp [correctionWires,hq])
          simp only [List.map_cons,ihc hcs]
          congr 1
          cases c with
          | Z a => simp only [renameCorrection,hc a (by simp [correctionWires])]
          | CZ a b => simp only [renameCorrection,hc a (by simp [correctionWires]),hc b (by simp [correctionWires])]
      simp only [renameInstr,head t (by simp [Instr.wires]),
        corr c0 (fun q hq => head q (by simp [Instr.wires,hq])),
        corr c1 (fun q hq => head q (by simp [Instr.wires,hq]))]

end ECDSAAdd.Entrant.RouteA.Rolling1588
end
