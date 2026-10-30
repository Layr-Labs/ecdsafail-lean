import ECDSAAdd.Submission.Entrant.MainPre

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

-- Q6 INTEGRATION ActualFree.lean
namespace ECDSAAdd.Entrant.OwnQ6Actual
open Arithmetic MappedCompressed
attribute [local irreducible] wires KernelOB5.segH Q5FusionFields.hostField5S OwnExitFuseQ5.hostMulS OwnExitFuseQ5.hostMul

theorem field_kernel_free (divide : Bool) :
    base 1541∉wires (OwnQ6Core5.kernel divide (OneBankCell5.ports base (base 2409))) :=
  Q6IntegrationActive.concrete_retired divide

theorem hosted_field_free (divide : Bool) : base 1541∉wires (KernelOB5.segH divide) :=
  OwnQ6FieldFree.segH_free field_kernel_free divide

theorem hosted_selected_field_free (divide : Bool) : base 1541∉wires (SW.segHS divide) :=
  OwnQ6FieldFree.segHS_free field_kernel_free divide

theorem entry_selected_free : base 1541∉wires Q5FusionFields.hostField5S := fun h =>
  hosted_field_free true ((@SW.InstrSub2.wires_sub Q5FusionFields.hostField5S (KernelOB5.segH true) Q5FusionFields.hostField5S_sub) h)

theorem exit_selected_free : base 1541∉wires OwnExitFuseQ5.hostMulS := fun h =>
  hosted_field_free false ((@LaneI.InstrSub.wires_sub OwnExitFuseQ5.hostMul (KernelOB5.segH false) OwnExitFuseQ5.hostMul_sub) ((@SW.InstrSub2.wires_sub OwnExitFuseQ5.hostMulS OwnExitFuseQ5.hostMul OwnExitFuseQ5.selHost.sub) h))
end ECDSAAdd.Entrant.OwnQ6Actual


-- Q6 INTEGRATION LateComponents-check.lean

-- BEGIN IntegerHost
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6IntegerHost
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed DirectSkywalk OffsetBorrowedCanonical History5
attribute [local irreducible] wires run Stack5.forward5 stackForwardT NativeFirstDirect.forward StackOB5.forward OB5.sig
def swap : Equiv.Perm Wire := Equiv.swap (base 1541) (base 719)

theorem pull_clean (s : State) (a : s.basis (base 1541)=false)
    (b : s.basis (base 719)=false) : pullState swap s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (swap q)=s.basis q
    by_cases h : q=base 1541
    · subst q; simp [swap,a,b]
    · by_cases h' : q=base 719
      · subst q; simp [swap,a,b]
      · rw [show swap q=q by exact Equiv.swap_apply_of_ne_of_ne h h']

theorem run_eq (P : Program) (s : State) (m : List Bool)
    (a : s.basis (base 1541)=false) (b : s.basis (base 719)=false)
    (c : (run P m s).basis (base 1541)=false)
    (d : (run P m s).basis (base 719)=false) :
    run (renameProgram swap P) m s=run P m s := by
  apply pullState_perm_injective swap
  rw [run_rename swap swap.injective,pull_clean s a b,pull_clean _ c d]


theorem integer719_free : base 719∉OB5.integerSites := by
  intro used
  obtain ⟨i,e,hi⟩ := (OB5.integerSites_mem _).mp used
  have same := base_injective e
  omega

theorem prefix719_free : base 719∉NativeFirstDirect.prefixSites base := by
  intro used
  simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with ((a|b)|c)|(a|b)
  · exact OwnPlusHost.not_block 719 0 257 (by omega) a
  · exact OwnPlusHost.not_block 719 770 258 (by omega) b
  · exact OwnPlusHost.not_block 719 1540 256 (by omega) c
  · exact (by decide : base 719≠base 1028) a
  · exact (by decide : base 719≠base 1797) b

theorem terminal1541 (x : Nat) (s : State)
    (h : W.CompressedCompactStage5 base x p 512 s.basis) :
    s.basis (base 1541)=false := by
  obtain ⟨raw,stage,eq⟩ := h
  have fields := (W.compactSkywalkStage_fields_iff base _ 512 (by omega) base_pool_nodup raw.basis).mp stage
  have carry : regValue (wireBlock base 1540 257) raw.basis=0 := fields.2.2.2.2.2.1
  have clean : raw.basis (base 1541)=false := (regValue_zero _ _).mp carry _ (by decide +kernel)
  have away : base 1541∉wires (History5.encodePrefix base 512) := by
    rw [History5.encodePrefix_512]
    intro used
    have support := History5.allEncode_history_support base 102 (by decide) used
    simp only [List.mem_toFinset,List.mem_append] at support
    rcases support with a|b
    · exact OwnPlusHost.not_block 1541 0 512 (by omega) a
    · exact OwnPlusHost.not_block 1541 1028 512 (by omega) b
  rw [eq,run_preserves_outside _ [] raw _ away]
  exact clean
theorem forward_terminal1541 (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (m2 : List Bool)
    (firstW : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis) :
    (run stackForwardT m2 s1).basis (base 1541)=false := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32≤2^256 := by norm_num [p]
  obtain ⟨t, ht⟩ : ∃t : State,run (Stack5.forward5 base 1 511) m2 s1=t := ⟨_,rfl⟩
  have terminal : W.CompressedCompactStage5 base x p 512 t.basis := by
    have raw := (Stack5.forward_spec base base_pool_nodup StackOB5.historyAbove x p 1 511
      hp0 hx0 hpo hp gap hx cop (by omega) s1 m2 (W.compactStage5_first base x p s1 firstW)).2
    rw [ht] at raw
    exact raw
  have eq : run stackForwardT m2 s1 = pullState (OB5.sig 511) t := by
    rw [←ht]
    exact (stackForwardT_run hn StackOB5.historyAbove x hx0 hx s1 m2 firstW).trans
      (StackOB5.forward_run x hx0 hx s1 m2 firstW)
  have fixed : OB5.sig 511 (base 1541)=base 1541 := by decide +kernel
  rw [eq]
  change t.basis (OB5.sig 511 (base 1541))=false
  rw [fixed]
  exact terminal1541 x _ terminal

theorem history1541_free (start : Nat) (hs : start+5≤512) (q : Fin 10) :
    History5.historyId start q ≠1541 := by
  have h:=History5.historyId_region start hs q
  omega

theorem sig1541 (i : Nat) (hi : i≤511) : OB5.sig i (base 1541)=base 1541 := by
  rw [OB5.sig_base i 1541 hi]
  split_ifs <;> first | omega | rfl
def firstPhase : Program := NativeFirstDirect.forward base ++ (stackForwardT ++ skywalkArithmeticClear base)
attribute [local irreducible] firstPhase

theorem firstPhase719_free : base 719∉wires firstPhase := by
  have native : base 719∉wires (NativeFirstDirect.forward base) := fun h =>
    prefix719_free (List.mem_toFinset.mp ((NativeFirstDirect.prefix_support base).1 h))
  have stack : base 719∉wires stackForwardT := fun h =>
    integer719_free ((StackOB5.support_gen 1 511 (by omega) (by omega)).1 _ (stackForwardT_subset h))
  have clear : base 719∉wires (skywalkArithmeticClear base) := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]
  simpa only [firstPhase,wires_append,Finset.mem_union,not_or] using ⟨native,stack,clear⟩

theorem input_clean (x y i : Nat) (s : State) (hin : SkywalkArithmeticInput base x y s.basis)
    (hi : i=719 ∨ i=1541) : s.basis (base i)=false := by
  apply hin.2.2 (base i)
  · rcases hi with rfl|rfl <;> decide +kernel
  · exact OwnPlusHost.not_block i 770 256 (by rcases hi with rfl|rfl <;> omega)
  · exact OwnPlusHost.not_block i 2056 256 (by rcases hi with rfl|rfl <;> omega)

theorem firstPhase1541_clean (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    (run firstPhase m s).basis (base 1541)=false := by
  rw [firstPhase,run_append,run_append]
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s
    (m.take (measurementCount (NativeFirstDirect.forward base))) hin
  have firstW := (W.compactSkywalkStage_one base _ _).mpr first
  have cleaned := forward_terminal1541 hn x hx0 hx _
    ((m.drop (measurementCount (NativeFirstDirect.forward base))).take (measurementCount stackForwardT)) firstW
  have away : base 1541∉wires (skywalkArithmeticClear base) := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]
  exact (run_preserves_outside _ _ _ _ away).trans cleaned

theorem firstPhase_state_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    run (renameProgram swap firstPhase) m s=run firstPhase m s := by
  apply run_eq
  · exact input_clean x Y.val 1541 s hin (Or.inr rfl)
  · exact input_clean x Y.val 719 s hin (Or.inl rfl)
  · exact firstPhase1541_clean hn x Y hx0 hx s m hin
  · exact (run_preserves_outside _ _ _ _ firstPhase719_free).trans
      (input_clean x Y.val 719 s hin (Or.inl rfl))
def lastPhase : Program := skywalkArithmeticClear base ++ (stackReverseT ++ NativeFirstKnown.inverse base)
attribute [local irreducible] lastPhase

theorem lastPhase719_free : base 719∉wires lastPhase := by
  have native : base 719∉wires (NativeFirstKnown.inverse base) := fun h =>
    prefix719_free (List.mem_toFinset.mp (NativeFirstKnown.inverse_support base h))
  have stack : base 719∉wires stackReverseT := fun h =>
    integer719_free ((StackOB5.support_gen 1 511 (by omega) (by omega)).2 _ (stackReverseT_subset h))
  have clear : base 719∉wires (skywalkArithmeticClear base) := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]
  simpa only [lastPhase,wires_append,Finset.mem_union,not_or] using ⟨clear,stack,native⟩

/-- Full arbitrary-record transfer needs only the old complete program's clean
output and the new field implementation's literal omission of1541. It imposes
no new promise on the original caller input. -/
theorem three_states_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (mp mf mr : List Bool) (F : Program)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (field_free : base 1541∉wires F)
    (out1541 : (run lastPhase mr (run F mf (run firstPhase mp s))).basis (base 1541)=false)
    (out719 : (run lastPhase mr (run F mf (run firstPhase mp s))).basis (base 719)=false) :
    run (renameProgram swap lastPhase) mr
      (run F mf (run (renameProgram swap firstPhase) mp s)) =
    run lastPhase mr (run F mf (run firstPhase mp s)) := by
  rw [firstPhase_state_eq hn x Y hx0 hx s mp hin]
  have mid1541 : (run F mf (run firstPhase mp s)).basis (base 1541)=false :=
    (run_preserves_outside _ _ _ _ field_free).trans (firstPhase1541_clean hn x Y hx0 hx s mp hin)
  have mid719 : (run F mf (run firstPhase mp s)).basis (base 719)=false :=
    (run_preserves_outside lastPhase mr _ _ lastPhase719_free).symm.trans out719
  exact run_eq lastPhase _ mr mid1541 mid719 out1541 out719

theorem wireFn2_719 (L : ControlledPointLayout) : wireFn2 L (base 719)=L.core.poolWire 719 := by rfl

theorem rename_1541_free (P : Program) (free : base 719∉wires P) :
    base 1541∉wires (renameProgram swap P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨old,member,eq⟩ := Finset.mem_image.mp used
  have back := congrArg swap eq
  simp only [swap,Equiv.swap_apply_self,Equiv.swap_apply_left] at back
  exact free (back ▸ member)

theorem wireFn2_1541 (L : ControlledPointLayout) : wireFn2 L (base 1541)=L.core.poolWire 1285 := by rfl

theorem final719_charged (L : ControlledPointLayout) : L.core.poolWire 719∈WrapperOB5.sites L := by
  have member : L.core.poolWire 719∈wireBlock L.core.poolWire 718 311 :=
    List.mem_map.mpr ⟨719,by simp only [List.mem_range'_1]; omega,rfl⟩
  simp only [WrapperOB5.sites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto


def q5First : Program := renameProgram Q5Global718.swap firstPhase
def q5Last : Program := renameProgram Q5Global718.swap lastPhase
attribute [local irreducible] q5First q5Last

private theorem q5first_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    run q5First m s=run firstPhase m s := by
  have same : firstPhase=Q5Global718.firstPhase := by unfold firstPhase Q5Global718.firstPhase; rfl
  unfold q5First
  rw [same]
  exact Q5Global718.firstPhase_state_eq hn x Y hx0 hx s m hin

theorem q5First719_free : base 719∉wires q5First := by
  unfold q5First
  exact OwnPlusHost.rename_avoid _ _ _ (by decide +kernel) firstPhase719_free

theorem q5Last719_free : base 719∉wires q5Last := by
  unfold q5Last
  exact OwnPlusHost.rename_avoid _ _ _ (by decide +kernel) lastPhase719_free

theorem q5First_state_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    run (renameProgram swap q5First) m s=run q5First m s := by
  apply run_eq
  · exact input_clean x Y.val 1541 s hin (Or.inr rfl)
  · exact input_clean x Y.val 719 s hin (Or.inl rfl)
  · rw [q5first_eq hn x Y hx0 hx s m hin]
    exact firstPhase1541_clean hn x Y hx0 hx s m hin
  · exact (run_preserves_outside _ _ _ _ q5First719_free).trans
      (input_clean x Y.val 719 s hin (Or.inl rfl))

theorem q5_three_states_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (mp mf mr : List Bool) (F : Program)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (field_free : base 1541∉wires F)
    (out1541 : (run q5Last mr (run F mf (run q5First mp s))).basis (base 1541)=false)
    (out719 : (run q5Last mr (run F mf (run q5First mp s))).basis (base 719)=false) :
    run (renameProgram swap q5Last) mr
      (run F mf (run (renameProgram swap q5First) mp s)) =
    run q5Last mr (run F mf (run q5First mp s)) := by
  rw [q5First_state_eq hn x Y hx0 hx s mp hin]
  have mid1541 : (run F mf (run q5First mp s)).basis (base 1541)=false := by
    rw [run_preserves_outside _ _ _ _ field_free,q5first_eq hn x Y hx0 hx s mp hin]
    exact firstPhase1541_clean hn x Y hx0 hx s mp hin
  have mid719 : (run F mf (run q5First mp s)).basis (base 719)=false :=
    (run_preserves_outside q5Last mr _ _ q5Last719_free).symm.trans out719
  exact run_eq q5Last _ mr mid1541 mid719 out1541 out719

end ECDSAAdd.Entrant.Q6IntegerHost

-- BEGIN FusionPhase
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6FusionPhase
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed DirectSkywalk CompressedAllocation Q6IntegerHost
attribute [local irreducible] run wires Q6IntegerHost.q5First Q6IntegerHost.q5Last

theorem outside_num (i : Nat) (hi : i=719∨i=1541) : base i∉wireBlock base 2056 256 :=
  OwnPlusHost.not_block i 2056 256 (by rcases hi with rfl|rfl <;> omega)

theorem q5First_pool : wires q5First⊆(skywalkPoolWires base).toFinset := by
  unfold q5First
  rw [renameProgram_support]
  intro q h
  obtain ⟨old,used,rfl⟩:=Finset.mem_image.mp h
  have oldPool : old∈skywalkPoolWires base := by
    apply List.mem_toFinset.mp
    apply Q5FusionPhase.firstPhase_pool
    simpa only [Q6IntegerHost.firstPhase,Q5Global718.firstPhase] using used
  apply List.mem_toFinset.mpr
  by_cases a:old=base 1026
  · subst old
    simpa only [Q5Global718.swap,Equiv.swap_apply_left] using
      arith_mem base 0 1798 718 (by omega) (by omega)
  · by_cases b:old=base 718
    · subst old
      simpa only [Q5Global718.swap,Equiv.swap_apply_right] using
        arith_mem base 0 1798 1026 (by omega) (by omega)
    · simpa only [Q5Global718.swap,Equiv.swap_apply_of_ne_of_ne a b] using oldPool

theorem firstPhase1541_paired (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b) :
    (run q5First m b).basis (base 1541)=false := by
  have agree := Q5FusionPhase.pool_agreement q5First q5First_pool a b m same (base 1541)
    (arith_mem base 0 1798 1541 (by omega) (by omega))
  have canonical : run q5First m a=run Q6IntegerHost.firstPhase m a := by
    simpa only [q5First,Q6IntegerHost.firstPhase,Q5Global718.firstPhase] using
      Q5Global718.firstPhase_state_eq hn x Y hx0 hx a m input
  exact agree.trans (canonical ▸ Q6IntegerHost.firstPhase1541_clean hn x Y hx0 hx a m input)

theorem firstPhase_eq_paired (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b) :
    run (renameProgram swap q5First) m b=run q5First m b := by
  have clean1541 : b.basis (base 1541)=false :=
    (same _ (outside_num 1541 (Or.inr rfl))).trans (input_clean x Y.val 1541 a input (Or.inr rfl))
  have clean719 : b.basis (base 719)=false :=
    (same _ (outside_num 719 (Or.inl rfl))).trans (input_clean x Y.val 719 a input (Or.inl rfl))
  exact run_eq q5First b m clean1541 clean719
    (firstPhase1541_paired hn x Y hx0 hx a b m input same)
    ((run_preserves_outside _ _ _ _ q5First719_free).trans clean719)

theorem three_states_eq_paired (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (mp mf mr : List Bool) (F : Program)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b)
    (field_free : base 1541∉wires F)
    (out1541 : (run q5Last mr (run F mf (run q5First mp b))).basis (base 1541)=false)
    (out719 : (run q5Last mr (run F mf (run q5First mp b))).basis (base 719)=false) :
    run (renameProgram swap q5Last) mr (run F mf (run (renameProgram swap q5First) mp b))=
      run q5Last mr (run F mf (run q5First mp b)) := by
  rw [firstPhase_eq_paired hn x Y hx0 hx a b mp input same]
  have mid1541 : (run F mf (run q5First mp b)).basis (base 1541)=false :=
    (run_preserves_outside _ _ _ _ field_free).trans (firstPhase1541_paired hn x Y hx0 hx a b mp input same)
  have mid719 : (run F mf (run q5First mp b)).basis (base 719)=false :=
    (run_preserves_outside q5Last mr _ _ q5Last719_free).symm.trans out719
  exact run_eq q5Last _ mr mid1541 mid719 out1541 out719

def kernel (F : Program) := q5First++(F++q5Last)
def relocated (F : Program) := renameProgram swap q5First++(F++renameProgram swap q5Last)
attribute [local irreducible] kernel relocated

theorem state_eq_of_frame (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (m : List Bool) (F : Program)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b)
    (field_free : base 1541∉wires F)
    (frame : ∀q,q∉wireBlock base 2056 256 → (run (kernel F) m b).basis q=a.basis q) :
    run (relocated F) m b=run (kernel F) m b := by
  have clean (i : Nat) (hi : i=719∨i=1541) : (run (kernel F) m b).basis (base i)=false :=
    (frame _ (outside_num i hi)).trans (input_clean x Y.val i a input hi)
  have h:=three_states_eq_paired hn x Y hx0 hx a b
    (m.take (measurementCount q5First))
    ((m.drop (measurementCount q5First)).take (measurementCount F))
    ((m.drop (measurementCount q5First)).drop (measurementCount F)) F input same field_free
    (by simpa only [kernel,run_append] using clean 1541 (Or.inr rfl))
    (by simpa only [kernel,run_append] using clean 719 (Or.inl rfl))
  simpa only [kernel,relocated,run_append,(renameProgram_counts swap q5First).2] using h

theorem relocated_1541_free (F : Program) (field_free : base 1541∉wires F) :
    base 1541∉wires (relocated F) := by
  rw [relocated,wires_append,wires_append]
  simpa only [Finset.mem_union,not_or] using
    ⟨rename_1541_free q5First q5First719_free,field_free,rename_1541_free q5Last q5Last719_free⟩

theorem relocated_counts (F : Program) :
    toffoliCount (relocated F)=toffoliCount (kernel F) ∧
    measurementCount (relocated F)=measurementCount (kernel F) := by
  have a:=renameProgram_counts swap q5First
  have b:=renameProgram_counts swap q5Last
  simp only [kernel,relocated,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
  trivial
end ECDSAAdd.Entrant.Q6FusionPhase

-- BEGIN FusionGeometry
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6FusionGeometry
open ECDSAAdd Arithmetic MappedCompressed Q6IntegerHost
attribute [local irreducible] wires run

theorem old_shape (F : Program) : Q6FusionPhase.kernel F=Q5FusionPhase.relocated F := by
  simp only [Q6FusionPhase.kernel,Q5FusionPhase.relocated,q5First,q5Last,
    Q6IntegerHost.firstPhase,Q6IntegerHost.lastPhase,Q5Global718.firstPhase,Q5Global718.lastPhase]

theorem counts (F : Program) :
    toffoliCount (Q6FusionPhase.relocated F)=toffoliCount (Q5FusionPhase.relocated F) ∧
    measurementCount (Q6FusionPhase.relocated F)=measurementCount (Q5FusionPhase.relocated F) := by
  simpa only [old_shape] using Q6FusionPhase.relocated_counts F

theorem slots (F : Program) :
    Challenge.gateSlots (Q6FusionPhase.relocated F)=Challenge.gateSlots (Q5FusionPhase.relocated F) := by
  simp only [Q6FusionPhase.relocated,Q5FusionPhase.relocated,q5First,q5Last,
    Q6IntegerHost.firstPhase,Q6IntegerHost.lastPhase,Q5Global718.firstPhase,Q5Global718.lastPhase,
    Challenge.gateSlots_append,Baselines.rename_gateSlots]

theorem physical (F : Program) (old : GatePhysical (Q5FusionPhase.relocated F)) :
    GatePhysical (Q6FusionPhase.relocated F) := by
  rw [←old_shape] at old
  simp only [Q6FusionPhase.kernel,gatePhysical_append] at old
  simp only [Q6FusionPhase.relocated,gatePhysical_append]
  exact ⟨gatePhysical_rename swap swap.injective _ old.1,
    old.2.1,gatePhysical_rename swap swap.injective _ old.2.2⟩

theorem swap_logical (q : Wire) (hq : q∈OB5Support.logicalSites) : swap q∈OB5Support.logicalSites := by
  have member (i : Nat) (hi : i=719∨i=1541) : base i∈OB5Support.logicalSites := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    rcases hi with rfl|rfl <;> omega
  by_cases a:q=base 1541
  · subst q;simpa only [swap,Equiv.swap_apply_left] using member 719 (Or.inl rfl)
  · by_cases b:q=base 719
    · subst q;simpa only [swap,Equiv.swap_apply_right] using member 1541 (Or.inr rfl)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem rename_support (P : Program) (old : wires P⊆OB5Support.logicalSites) :
    wires (renameProgram swap P)⊆OB5Support.logicalSites := by
  rw [renameProgram_support]
  intro q h
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp h
  exact swap_logical w (old hw)

theorem support (F : Program) (old : wires (Q5FusionPhase.relocated F)⊆OB5Support.logicalSites) :
    wires (Q6FusionPhase.relocated F)⊆OB5Support.logicalSites := by
  rw [←old_shape] at old
  simp only [Q6FusionPhase.kernel,wires_append,Finset.union_subset_iff] at old
  simp only [Q6FusionPhase.relocated,wires_append,Finset.union_subset_iff]
  exact ⟨rename_support _ old.1,old.2.1,rename_support _ old.2.2⟩

theorem avoids (F : Program) (q : Wire) (ha : q≠base 1541) (hb : q≠base 719)
    (old : q∉wires (Q5FusionPhase.relocated F)) : q∉wires (Q6FusionPhase.relocated F) := by
  rw [←old_shape] at old
  simp only [Q6FusionPhase.kernel,wires_append,Finset.mem_union,not_or] at old
  simp only [Q6FusionPhase.relocated,wires_append,Finset.mem_union,not_or]
  have fix : swap q=q := Equiv.swap_apply_of_ne_of_ne ha hb
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix old.1,old.2.1,OwnPlusHost.rename_avoid _ _ _ fix old.2.2⟩

theorem sel (F G : Program) (h : SW.Sel (base 2400) 1020 G F) :
    SW.Sel (base 2400) 1020 (Q6FusionPhase.relocated G) (Q6FusionPhase.relocated F) := by
  have fp : base 2400∉wires q5First := by
    simpa only [q5First,Q6IntegerHost.firstPhase,Q5Global718.firstPhase] using OwnQ5SW.renamed_first_away
  have lp : base 2400∉wires q5Last := by
    simpa only [q5Last,Q6IntegerHost.lastPhase,Q5Global718.lastPhase] using OwnQ5SW.renamed_last_away
  have fix : swap (base 2400)=base 2400 := by decide +kernel
  have hh:=(SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix fp)).append
    (h.append (SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix lp)))
  simpa only [Q6FusionPhase.relocated,Nat.zero_add,Nat.add_zero] using hh
end ECDSAAdd.Entrant.Q6FusionGeometry

-- BEGIN FusionKernels
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnEntryFuseQ6
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5 Q5FusionFields
attribute [local irreducible] run wires
def kernel5 : Program := Q6FusionPhase.relocated Q5FusionFields.hostField5
attribute [local irreducible] kernel5
theorem old_shape_kernel5 : Q6FusionPhase.kernel Q5FusionFields.hostField5=OwnEntryFuseQ5.kernel5 := by
  simpa only [OwnEntryFuseQ5.kernel5] using Q6FusionGeometry.old_shape Q5FusionFields.hostField5
theorem kernel5_support : wires kernel5⊆OB5Support.logicalSites := by
  simpa only [kernel5,OwnEntryFuseQ5.kernel5] using Q6FusionGeometry.support Q5FusionFields.hostField5 (by
    simpa only [OwnEntryFuseQ5.kernel5] using (OwnEntryFuseQ5.kernel5_support : wires OwnEntryFuseQ5.kernel5⊆OB5Support.logicalSites))
theorem kernel5_physical : GatePhysical kernel5 := by
  simpa only [kernel5,OwnEntryFuseQ5.kernel5] using Q6FusionGeometry.physical Q5FusionFields.hostField5 (by
    simpa only [OwnEntryFuseQ5.kernel5] using (OwnEntryFuseQ5.kernel5_physical : GatePhysical OwnEntryFuseQ5.kernel5))
theorem kernel5_counts_eq : toffoliCount kernel5=toffoliCount OwnEntryFuseQ5.kernel5 ∧
    measurementCount kernel5=measurementCount OwnEntryFuseQ5.kernel5 := by
  simpa only [kernel5,OwnEntryFuseQ5.kernel5] using Q6FusionGeometry.counts Q5FusionFields.hostField5
theorem kernel5_slots_eq : Challenge.gateSlots kernel5=Challenge.gateSlots OwnEntryFuseQ5.kernel5 := by
  simpa only [kernel5,OwnEntryFuseQ5.kernel5] using Q6FusionGeometry.slots Q5FusionFields.hostField5
theorem kernel5_1541_free (free : base 1541∉wires Q5FusionFields.hostField5) : base 1541∉wires kernel5 := by
  simpa only [kernel5] using Q6FusionPhase.relocated_1541_free Q5FusionFields.hostField5 free
theorem kernel5_correct (free : base 1541∉wires Q5FusionFields.hostField5)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  have old:=OwnEntryFuseQ5.kernel5_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel Q5FusionFields.hostField5) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m Q5FusionFields.hostField5 hin same free frame
  simpa only [kernel5,eq,old_shape_kernel5] using old
def kernel5S : Program := Q6FusionPhase.relocated Q5FusionFields.hostField5S
attribute [local irreducible] kernel5S
theorem old_shape_kernel5S : Q6FusionPhase.kernel Q5FusionFields.hostField5S=OwnEntryFuseQ5.kernel5S := by
  simpa only [OwnEntryFuseQ5.kernel5S] using Q6FusionGeometry.old_shape Q5FusionFields.hostField5S
theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites := by
  simpa only [kernel5S,OwnEntryFuseQ5.kernel5S] using Q6FusionGeometry.support Q5FusionFields.hostField5S (by
    simpa only [OwnEntryFuseQ5.kernel5S] using (OwnEntryFuseQ5.kernel5S_support : wires OwnEntryFuseQ5.kernel5S⊆OB5Support.logicalSites))
theorem kernel5S_physical : GatePhysical kernel5S := by
  simpa only [kernel5S,OwnEntryFuseQ5.kernel5S] using Q6FusionGeometry.physical Q5FusionFields.hostField5S (by
    simpa only [OwnEntryFuseQ5.kernel5S] using (OwnEntryFuseQ5.kernel5S_physical : GatePhysical OwnEntryFuseQ5.kernel5S))
theorem kernel5S_counts_eq : toffoliCount kernel5S=toffoliCount OwnEntryFuseQ5.kernel5S ∧
    measurementCount kernel5S=measurementCount OwnEntryFuseQ5.kernel5S := by
  simpa only [kernel5S,OwnEntryFuseQ5.kernel5S] using Q6FusionGeometry.counts Q5FusionFields.hostField5S
theorem kernel5S_slots_eq : Challenge.gateSlots kernel5S=Challenge.gateSlots OwnEntryFuseQ5.kernel5S := by
  simpa only [kernel5S,OwnEntryFuseQ5.kernel5S] using Q6FusionGeometry.slots Q5FusionFields.hostField5S
theorem kernel5S_1541_free (free : base 1541∉wires Q5FusionFields.hostField5S) : base 1541∉wires kernel5S := by
  simpa only [kernel5S] using Q6FusionPhase.relocated_1541_free Q5FusionFields.hostField5S free
theorem kernel5S_correct (free : base 1541∉wires Q5FusionFields.hostField5S)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=OwnEntryFuseQ5.kernel5S_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel Q5FusionFields.hostField5S) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5S] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m Q5FusionFields.hostField5S hin same free frame
  simpa only [kernel5S,eq,old_shape_kernel5S] using old
theorem selKernel5 : SW.Sel (base 2400) 1020 kernel5S kernel5 := by
  simpa only [kernel5,kernel5S] using Q6FusionGeometry.sel Q5FusionFields.hostField5 Q5FusionFields.hostField5S Q5FusionFields.selHostField5
end ECDSAAdd.Entrant.OwnEntryFuseQ6
namespace ECDSAAdd.Entrant.OwnExitFuseQ6
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5 Q5FusionFields
attribute [local irreducible] run wires
def kernel : Program := Q6FusionPhase.relocated OwnExitFuseQ5.hostMul
attribute [local irreducible] kernel
theorem old_shape_kernel : Q6FusionPhase.kernel OwnExitFuseQ5.hostMul=OwnExitFuseQ5.kernel := by
  simpa only [OwnExitFuseQ5.kernel] using Q6FusionGeometry.old_shape OwnExitFuseQ5.hostMul
theorem kernel_support : wires kernel⊆OB5Support.logicalSites := by
  simpa only [kernel,OwnExitFuseQ5.kernel] using Q6FusionGeometry.support OwnExitFuseQ5.hostMul OwnExitFuseQ5.kernel_support
theorem kernel_physical : GatePhysical kernel := by
  simpa only [kernel,OwnExitFuseQ5.kernel] using Q6FusionGeometry.physical OwnExitFuseQ5.hostMul OwnExitFuseQ5.kernel_physical
theorem kernel_counts_eq : toffoliCount kernel=toffoliCount OwnExitFuseQ5.kernel ∧
    measurementCount kernel=measurementCount OwnExitFuseQ5.kernel := by
  simpa only [kernel,OwnExitFuseQ5.kernel] using Q6FusionGeometry.counts OwnExitFuseQ5.hostMul
theorem kernel_slots_eq : Challenge.gateSlots kernel=Challenge.gateSlots OwnExitFuseQ5.kernel := by
  simpa only [kernel,OwnExitFuseQ5.kernel] using Q6FusionGeometry.slots OwnExitFuseQ5.hostMul
theorem kernel_1541_free (free : base 1541∉wires OwnExitFuseQ5.hostMul) : base 1541∉wires kernel := by
  simpa only [kernel] using Q6FusionPhase.relocated_1541_free OwnExitFuseQ5.hostMul free
theorem kernel_correct (free : base 1541∉wires OwnExitFuseQ5.hostMul)
    (hn : (skywalkSharedWires base).Nodup) (hlo : HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    let out := run kernel m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=
      centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=OwnExitFuseQ5.kernel_correct hn hlo ho hf x Y hx0 hx s m input hg0 hs0
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel OwnExitFuseQ5.hostMul) m s).basis q=s.basis q := by
    simpa only [old_shape_kernel,skywalkArithmeticNumerator] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s s m OwnExitFuseQ5.hostMul input
    (fun _ _=>rfl) free frame
  simpa only [kernel,eq,old_shape_kernel] using old
def kernelS : Program := Q6FusionPhase.relocated OwnExitFuseQ5.hostMulS
attribute [local irreducible] kernelS
theorem old_shape_kernelS : Q6FusionPhase.kernel OwnExitFuseQ5.hostMulS=OwnExitFuseQ5.kernelS := by
  simpa only [OwnExitFuseQ5.kernelS] using Q6FusionGeometry.old_shape OwnExitFuseQ5.hostMulS
theorem kernelS_support : wires kernelS⊆OB5Support.logicalSites := by
  simpa only [kernelS,OwnExitFuseQ5.kernelS] using Q6FusionGeometry.support OwnExitFuseQ5.hostMulS OwnExitFuseQ5.kernelS_support
theorem kernelS_physical : GatePhysical kernelS := by
  simpa only [kernelS,OwnExitFuseQ5.kernelS] using Q6FusionGeometry.physical OwnExitFuseQ5.hostMulS OwnExitFuseQ5.kernelS_physical
theorem kernelS_counts_eq : toffoliCount kernelS=toffoliCount OwnExitFuseQ5.kernelS ∧
    measurementCount kernelS=measurementCount OwnExitFuseQ5.kernelS := by
  simpa only [kernelS,OwnExitFuseQ5.kernelS] using Q6FusionGeometry.counts OwnExitFuseQ5.hostMulS
theorem kernelS_slots_eq : Challenge.gateSlots kernelS=Challenge.gateSlots OwnExitFuseQ5.kernelS := by
  simpa only [kernelS,OwnExitFuseQ5.kernelS] using Q6FusionGeometry.slots OwnExitFuseQ5.hostMulS
theorem kernelS_1541_free (free : base 1541∉wires OwnExitFuseQ5.hostMulS) : base 1541∉wires kernelS := by
  simpa only [kernelS] using Q6FusionPhase.relocated_1541_free OwnExitFuseQ5.hostMulS free
theorem kernelS_correct (free : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    (run kernelS m s).phase=s.phase ∧
    regValue (skywalkArithmeticNumerator base) (run kernelS m s).basis=
      centerWord (Y*(x:Fp)/2) ∧
    ∀ q,q∉skywalkArithmeticNumerator base → (run kernelS m s).basis q=s.basis q := by
  have old:=OwnExitFuseQ5.kernelS_correct hn hlo ho hf x Y hx0 hx s m hin hg0 hs0
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel OwnExitFuseQ5.hostMulS) m s).basis q=s.basis q := by
    simpa only [old_shape_kernelS,skywalkArithmeticNumerator] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s s m OwnExitFuseQ5.hostMulS hin
    (fun _ _=>rfl) free frame
  simpa only [kernelS,eq,old_shape_kernelS] using old
theorem selKernel : SW.Sel (base 2400) 1020 kernelS kernel := by
  simpa only [kernel,kernelS] using Q6FusionGeometry.sel OwnExitFuseQ5.hostMul OwnExitFuseQ5.hostMulS OwnExitFuseQ5.selHost
end ECDSAAdd.Entrant.OwnExitFuseQ6

-- BEGIN FusionCallers
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section
namespace ECDSAAdd.Entrant.OwnEntryFuseQ6
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires

private theorem mapped_regS (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

/-- A renamed replay receives the same pool as a canonical virtual state,
while its actual numerator has already been half-centered. -/
theorem kernelTransferS (freeS : base 1541∉wires Q5FusionFields.hostField5S) (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool) (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain) (bSite : base 2400∈domain)
    (sites : wires OwnEntryFuseQ6.kernel5S⊆domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (phase : t.phase=s.phase) (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (renameProgram f OwnEntryFuseQ6.kernel5S) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let a := laneLogicalInput domain f s
  let b := laneLogicalInput domain f t
  have aBits (q : Wire) (hq : q∈domain) : a.basis q=s.basis (f q) := by
    simp only [a,laneLogicalInput,if_pos hq]
  have bBits (q : Wire) (hq : q∈domain) : b.basis q=t.basis (f q) := by
    simp only [b,laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : a.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=X
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a,laneLogicalInput,if_neg used]
  have outside (q : Wire) (hq : q∈domain) (haway : q∉wireBlock base 2056 256) : f q∉L.point.y := by
    rw [←numeratorMap]
    intro bad
    obtain ⟨r,hr,he⟩ := List.mem_map.mp bad
    have eq : q=r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀q,q∉wireBlock base 2056 256 → b.basis q=a.basis q := by
    intro q hq
    by_cases used : q∈domain
    · rw [bBits q used,aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a,b,laneLogicalInput,if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    rw [mapped_regS f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
    exact half
  have phases : b.phase=a.phase := by change t.phase=s.phase; exact phase
  have strong := OwnEntryFuseQ6.kernel5S_correct freeS hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective OwnEntryFuseQ6.kernel5S sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (mapped_regS f _ (run OwnEntryFuseQ6.kernel5S m b).basis
      (run (renameProgram f OwnEntryFuseQ6.kernel5S) m t).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q∈domain.image f
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp image
      have away : r∉skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨r,mem,rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain OwnEntryFuseQ6.kernel5S sites m t q image).trans (same q hq)


end ECDSAAdd.Entrant.OwnEntryFuseQ6
end
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnEntryFuseQ6
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires toffoliCount measurementCount
def arithEntryS (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) OwnEntryFuseQ6.kernel5S

theorem arithEntryS_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (arithEntryS L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ kernel5S_support

theorem arithEntryS_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (arithEntryS L) := by
  apply gatePhysical_rename_support (wireFn2 L) OwnEntryFuseQ6.kernel5S
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (OwnEntryFuseQ6.kernel5S_support ha)) b
      (ArithmeticOB5.logical_sub_old (OwnEntryFuseQ6.kernel5S_support hb)) eq
  · exact OwnEntryFuseQ6.kernel5S_physical

theorem arithEntryS_counts_eq (L : ControlledPointLayout) :
    toffoliCount (arithEntryS L)=toffoliCount (EntryFuse.arithEntryS L) ∧
    measurementCount (arithEntryS L)=measurementCount (EntryFuse.arithEntryS L) := by
  have c:=kernel5S_counts_eq
  have a:=renameProgram_counts (wireFn2 L) kernel5S
  have b:=renameProgram_counts (wireFn2 L) OwnEntryFuseQ5.kernel5S
  simpa only [arithEntryS,EntryFuse.arithEntryS,a.1,a.2,b.1,b.2] using c

theorem arithEntryS_gateSlots_le (L : ControlledPointLayout) :
    Challenge.gateSlots (arithEntryS L)≤20500006 := by
  simpa only [arithEntryS,Baselines.rename_gateSlots] using kernel5S_slots_eq.trans_le OwnEntryFuseQ5.kernel5S_gateSlots_le

private theorem divisor_sitesS : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))

private theorem numerator_sitesS : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))

private theorem control_siteS : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem arithEntryS_correct (freeS : base 1541∉wires Q5FusionFields.hostField5S) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (arithEntryS L) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  exact kernelTransferS freeS L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    divisor_sitesS numerator_sitesS control_siteS (OwnEntryFuseQ6.kernel5S_support.trans ArithmeticOB5.logical_sub_old)
    logicalND hlo logicalAway logicalReplay X Y B hX0 hX s t m hb hx hy clean phase same half

attribute [local irreducible] arithEntryS arithS

theorem arithEntryS_eq (freeS : base 1541∉wires Q5FusionFields.hostField5S) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    run (arithEntryS L) m t=run (arithS L false) [] s := by
  have newer := arithEntryS_correct freeS L hw hn logicalND hlo logicalAway logicalReplay X Y B hX0 hX
    s t m hb hx hy clean phase same half
  have older := arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue : regValue L.point.y (run (arithEntryS L) m t).basis =
      regValue L.point.y (run (arithS L false) [] s).basis := by
    rw [newer.2.1,older.2.1]
    simp [skywalkArithmeticResult,ZMod.natCast_zmod_val]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm

end ECDSAAdd.Entrant.OwnEntryFuseQ6
end


namespace ECDSAAdd.Entrant.OwnEntryFuseQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
open Challenge Baselines
def fusedDivisionF (L : ControlledPointLayout) (k : Fp) : Program :=
  fusedY L k ++ arithEntryS L

section EntryStep
attribute [local irreducible] run arithEntryS arithS fusedY fastConstAdd

theorem fusedDivisionF_step (freeS : base 1541∉wires Q5FusionFields.hostField5S) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (fusedDivisionF L k)
      (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin) := by
  intro s m v
  let Z : Fp := Y+(if G then k else 0)
  let n := measurementCount (fusedY L k)
  let a := run (fusedY L k) (m.take n) s
  let c := run (fastConstAdd L L.point.y k) [] s
  have oldAdd := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep := fastStep_addY L hw hn X Y G origin k s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := oldStep.2
  have fused := fusedY_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase=s.phase ∧ regValue L.point.y a.basis=
    centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
    ∀q,q∉L.point.y → a.basis q=s.basis q at fused
  change c.phase=s.phase ∧ regValue L.point.y c.basis=(Y.val+(if G then k.val else 0))%p ∧
    ∀q,q∉L.point.y → c.basis q=s.basis q at oldAdd
  have phase : a.phase=c.phase := fused.1.trans oldAdd.1.symm
  have same (q : Wire) (hq : q∉L.point.y) : a.basis q=c.basis q :=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half : regValue L.point.y a.basis=centerWord (Z/2) := by
    simpa only [v.generic,Z] using fused.2.1
  have hp : 0<X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have equal := arithEntryS_eq freeS L hw hn logicalND hlo logicalAway logicalReplay X.val Z G hp X.isLt
    c a (m.drop n) canonical.generic canonical.x canonical.y canonical.clean phase same half
  have eqProgram : run (fusedDivisionF L k) m s=run (arithS L false) [] c := by
    simp only [fusedDivisionF,run_append]
    change run (arithEntryS L) (m.drop n) a=run (arithS L false) [] c
    exact equal
  have old := arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1,?_⟩
  simpa only [Z,Bool.false_eq_true,if_false] using old.2

end EntryStep
end ECDSAAdd.Entrant.OwnEntryFuseQ6
namespace ECDSAAdd.Entrant.OwnExitFuseQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 OwnExitFuseQ5
attribute [local irreducible] run wires
def arithExit (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) kernelS
attribute [local irreducible] arithExit

theorem arithExit_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (arithExit L)⊆(OB5Support.sites L).toFinset := by
  unfold arithExit
  exact OB5Support.placed_support_logical L hw _ kernelS_support
theorem arithExit_correct (freeS : base 1541∉wires OwnExitFuseQ5.hostMulS) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (hX : X < p) (hX0 : 0 < X) (hY : Y < p)
    (s : State) (m : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (arithExit L) m s).phase=s.phase ∧
    regValue L.point.y (run (arithExit L) m s).basis=
      centerWord (((Y:Fp)*(X:Fp))/2) ∧
    ∀q,q∉L.point.y → (run (arithExit L) m s).basis q=s.basis q := by
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  rcases placement2 L hw hn with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,
    selectorG,selectorS,zeroFlag⟩
  have dx : (wireBlock base 770 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have dy : (wireBlock base 2056 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have result := wordTransfer L (wireFn2 L) OB5Support.logicalSites
    (fun a ha b hb eq => injective a (ArithmeticOB5.logical_sub_old ha) b
      (ArithmeticOB5.logical_sub_old hb) eq)
    divisorMap numeratorMap
    (fun q hq used hx hy => sharedWork q hq (ArithmeticOB5.logical_sub_old used) hx hy)
    selectorG selectorS dx dy X (Y:Fp) (centerWord (((Y:Fp)*(X:Fp))/2))
    s m hx (hy.trans yValue.symm) hc
    kernelS kernelS_support
    (fun t records input hg hs => kernelS_correct freeS
      config.1 above config.2.1 config.2.2 X (Y:Fp) hX0 hX t records input hg hs)
  simpa only [arithExit] using result

theorem arithExit_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (arithExit L) := by
  unfold arithExit
  apply gatePhysical_rename_support (wireFn2 L) kernelS
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (kernelS_support ha)) b
      (ArithmeticOB5.logical_sub_old (kernelS_support hb)) eq
  · exact kernelS_physical

theorem arithExit_counts_eq (L : ControlledPointLayout) :
    toffoliCount (arithExit L)=toffoliCount (OwnExitFuseQ5.arithExit L) ∧
    measurementCount (arithExit L)=measurementCount (OwnExitFuseQ5.arithExit L) := by
  have c:=kernelS_counts_eq
  have a:=renameProgram_counts (wireFn2 L) kernelS
  have b:=renameProgram_counts (wireFn2 L) OwnExitFuseQ5.kernelS
  simpa only [arithExit,OwnExitFuseQ5.arithExit,a.1,a.2,b.1,b.2] using c

theorem arithExit_slots_le (L : ControlledPointLayout) : Challenge.gateSlots (arithExit L)≤20500006 := by
  simpa only [arithExit,Baselines.rename_gateSlots] using kernelS_slots_eq.trans_le OwnExitFuseQ5.kernelS_slots_le
end ECDSAAdd.Entrant.OwnExitFuseQ6

-- BEGIN FusionOmissions
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6FusionOmissions
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 CompressedPointDialog
attribute [local irreducible] wires
 OwnEntryFuseQ6.kernel5S OwnExitFuseQ6.kernelS
private theorem placed (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (P : Program) (hp : wires P⊆OB5Support.logicalSites) (i k : Nat)
 (hi : base i∈OB5Support.logicalSites) (hm : wireFn2 L (base i)=L.core.poolWire k)
 (free : base i∉wires P) : L.core.poolWire k∉wires (renameProgram (wireFn2 L) P) := by
 rw [renameProgram_support]
 intro h
 obtain ⟨old,used,eq⟩ := Finset.mem_image.mp h
 have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
 have back := (placement2 L hw hn).injectiveOnSlots old
   (ArithmeticOB5.logical_sub_old (hp used)) (base i) (ArithmeticOB5.logical_sub_old hi) mapped
 exact free (back ▸ used)
private theorem logical (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
 base i∈OB5Support.logicalSites := by
 simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
 refine ⟨i,?_,rfl⟩
 simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 omega
private theorem entry_old (i : Nat) (hi : i∈[2312,766,765,767,1026]) : base i∉wires OwnEntryFuseQ5.kernel5S := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl|rfl|rfl|rfl|rfl
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnParityHost.kernel_parity_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnPlusFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnGuardFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnMinusFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact OwnEntryFuseQ5.kernel5S_1026_free
theorem entry_avoids (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (freeS : base 1541∉wires Q5FusionFields.hostField5S) (k : Nat)
 (hk : k∈[1800,766,765,767,770,1285]) :
 L.core.poolWire k∉wires (OwnEntryFuseQ6.arithEntryS L) := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
 rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
 · apply placed L hw hn OwnEntryFuseQ6.kernel5S OwnEntryFuseQ6.kernel5S_support 2312 1800
     (logical 2312 (by simp)) (by rfl)
   have h := Q6FusionGeometry.avoids Q5FusionFields.hostField5S (base 2312) (by decide +kernel) (by decide +kernel)
     (by simpa only [OwnEntryFuseQ5.kernel5S] using entry_old 2312 (by simp))
   simpa only [OwnEntryFuseQ6.kernel5S] using h
 · apply placed L hw hn OwnEntryFuseQ6.kernel5S OwnEntryFuseQ6.kernel5S_support 766 766
     (logical 766 (by simp)) (by rfl)
   have h := Q6FusionGeometry.avoids Q5FusionFields.hostField5S (base 766) (by decide +kernel) (by decide +kernel)
     (by simpa only [OwnEntryFuseQ5.kernel5S] using entry_old 766 (by simp))
   simpa only [OwnEntryFuseQ6.kernel5S] using h
 · apply placed L hw hn OwnEntryFuseQ6.kernel5S OwnEntryFuseQ6.kernel5S_support 765 765
     (logical 765 (by simp)) (by rfl)
   have h := Q6FusionGeometry.avoids Q5FusionFields.hostField5S (base 765) (by decide +kernel) (by decide +kernel)
     (by simpa only [OwnEntryFuseQ5.kernel5S] using entry_old 765 (by simp))
   simpa only [OwnEntryFuseQ6.kernel5S] using h
 · apply placed L hw hn OwnEntryFuseQ6.kernel5S OwnEntryFuseQ6.kernel5S_support 767 767
     (logical 767 (by simp)) (by rfl)
   have h := Q6FusionGeometry.avoids Q5FusionFields.hostField5S (base 767) (by decide +kernel) (by decide +kernel)
     (by simpa only [OwnEntryFuseQ5.kernel5S] using entry_old 767 (by simp))
   simpa only [OwnEntryFuseQ6.kernel5S] using h
 · apply placed L hw hn OwnEntryFuseQ6.kernel5S OwnEntryFuseQ6.kernel5S_support 1026 770
     (logical 1026 (by simp)) (by rfl)
   have h := Q6FusionGeometry.avoids Q5FusionFields.hostField5S (base 1026) (by decide +kernel) (by decide +kernel)
     (by simpa only [OwnEntryFuseQ5.kernel5S] using entry_old 1026 (by simp))
   simpa only [OwnEntryFuseQ6.kernel5S] using h
 · apply placed L hw hn OwnEntryFuseQ6.kernel5S OwnEntryFuseQ6.kernel5S_support 1541 1285
     (logical 1541 (by simp)) (by rfl)
   exact OwnEntryFuseQ6.kernel5S_1541_free freeS
private theorem exit_old (i : Nat) (hi : i∈[2312,766,765,767,1026]) : base i∉wires OwnExitFuseQ5.kernelS := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl|rfl|rfl|rfl|rfl
 · exact fun used => OwnQ5Integer.preserve_avoid false _ (by decide +kernel) (by decide +kernel)
     (OwnParityHost.kernel_parity_free false) (OwnExitFuseQ5.kernel_sub.wires_sub (OwnExitFuseQ5.selKernel.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid false _ (by decide +kernel) (by decide +kernel)
     (OwnPlusFinal.kernel_free false) (OwnExitFuseQ5.kernel_sub.wires_sub (OwnExitFuseQ5.selKernel.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid false _ (by decide +kernel) (by decide +kernel)
     (OwnGuardFinal.kernel_free false) (OwnExitFuseQ5.kernel_sub.wires_sub (OwnExitFuseQ5.selKernel.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid false _ (by decide +kernel) (by decide +kernel)
     (OwnMinusFinal.kernel_free false) (OwnExitFuseQ5.kernel_sub.wires_sub (OwnExitFuseQ5.selKernel.sub.wires_sub used))
 · exact OwnExitFuseQ5.kernelS_1026_free
theorem exit_avoids (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (freeS : base 1541∉wires OwnExitFuseQ5.hostMulS) (k : Nat)
 (hk : k∈[1800,766,765,767,770,1285]) :
 L.core.poolWire k∉wires (OwnExitFuseQ6.arithExit L) := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
 rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
 · apply placed L hw hn OwnExitFuseQ6.kernelS OwnExitFuseQ6.kernelS_support 2312 1800
     (logical 2312 (by simp)) (by rfl)
   have h := Q6FusionGeometry.avoids OwnExitFuseQ5.hostMulS (base 2312) (by decide +kernel) (by decide +kernel)
     (by simpa only [OwnExitFuseQ5.kernelS] using exit_old 2312 (by simp))
   simpa only [OwnExitFuseQ6.kernelS] using h
 · apply placed L hw hn OwnExitFuseQ6.kernelS OwnExitFuseQ6.kernelS_support 766 766
     (logical 766 (by simp)) (by rfl)
   have h := Q6FusionGeometry.avoids OwnExitFuseQ5.hostMulS (base 766) (by decide +kernel) (by decide +kernel)
     (by simpa only [OwnExitFuseQ5.kernelS] using exit_old 766 (by simp))
   simpa only [OwnExitFuseQ6.kernelS] using h
 · apply placed L hw hn OwnExitFuseQ6.kernelS OwnExitFuseQ6.kernelS_support 765 765
     (logical 765 (by simp)) (by rfl)
   have h := Q6FusionGeometry.avoids OwnExitFuseQ5.hostMulS (base 765) (by decide +kernel) (by decide +kernel)
     (by simpa only [OwnExitFuseQ5.kernelS] using exit_old 765 (by simp))
   simpa only [OwnExitFuseQ6.kernelS] using h
 · apply placed L hw hn OwnExitFuseQ6.kernelS OwnExitFuseQ6.kernelS_support 767 767
     (logical 767 (by simp)) (by rfl)
   have h := Q6FusionGeometry.avoids OwnExitFuseQ5.hostMulS (base 767) (by decide +kernel) (by decide +kernel)
     (by simpa only [OwnExitFuseQ5.kernelS] using exit_old 767 (by simp))
   simpa only [OwnExitFuseQ6.kernelS] using h
 · apply placed L hw hn OwnExitFuseQ6.kernelS OwnExitFuseQ6.kernelS_support 1026 770
     (logical 1026 (by simp)) (by rfl)
   have h := Q6FusionGeometry.avoids OwnExitFuseQ5.hostMulS (base 1026) (by decide +kernel) (by decide +kernel)
     (by simpa only [OwnExitFuseQ5.kernelS] using exit_old 1026 (by simp))
   simpa only [OwnExitFuseQ6.kernelS] using h
 · apply placed L hw hn OwnExitFuseQ6.kernelS OwnExitFuseQ6.kernelS_support 1541 1285
     (logical 1541 (by simp)) (by rfl)
   exact OwnExitFuseQ6.kernelS_1541_free freeS
end ECDSAAdd.Entrant.Q6FusionOmissions

-- BEGIN SquareHostCurrent
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6SquareHost
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires OwnQ5Square.program
private theorem q5_Square770_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem original_spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1537∉wires (Square5Placement.square5 L) := by
  rw [Square5Placement.square5,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=q5_Square770_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1537 (by omega))
  · have away:=q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1537 (by omega))
  · have away:=q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1537 (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1537 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1537 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

theorem spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1537∉wires (OwnQ4Square.program L) := by
  have fix (a b : Nat) (ha : a<2613) (hb : b<2613) (hna : a≠1537) (hnb : b≠1537) :
      (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire 1537)=L.core.poolWire 1537 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro eq;exact hna ((pool_inj L hw hn 1537 a (by omega) ha eq).symm)
    · intro eq;exact hnb ((pool_inj L hw hn 1537 b (by omega) hb eq).symm)
  have p : L.core.poolWire 1537∉wires (OwnPlusSquare.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix 766 1530 (by omega) (by omega) (by omega) (by omega)) (original_spare_free L hw hn)
  have g : L.core.poolWire 1537∉wires (OwnGuardSquare.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix 765 1531 (by omega) (by omega) (by omega) (by omega)) p
  exact OwnPlusHost.rename_avoid _ _ _ (fix 767 1532 (by omega) (by omega) (by omega) (by omega)) g

theorem current_spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1537 ∉ wires (OwnQ5Square.program L) := by
  have fix : OwnQ5Square.swap L (L.core.poolWire 1537)=L.core.poolWire 1537 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have := pool_inj L hw hn 1537 770 (by omega) (by omega) h
      omega
    · intro h
      have := pool_inj L hw hn 1537 1536 (by omega) (by omega) h
      omega
  unfold OwnQ5Square.program
  exact OwnPlusHost.rename_avoid _ _ _ fix (spare_free L hw hn)

def swap (L : ControlledPointLayout) : Equiv.Perm Wire :=
  Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)
def program (L : ControlledPointLayout) : Program := renameProgram (swap L) (OwnQ5Square.program L)
attribute [local irreducible] program

theorem pool (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q∈L.dialogPool,swap L q∈L.dialogPool := by
  intro q hq
  by_cases a:q=L.core.poolWire 1285
  · subst q; simpa only [swap,Equiv.swap_apply_left] using Square5Placement.pool_member L hw 1537 (by omega)
  · by_cases b:q=L.core.poolWire 1537
    · subst q; simpa only [swap,Equiv.swap_apply_right] using Square5Placement.pool_member L hw 1285 (by omega)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem outside (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q,q∉L.dialogPool → swap L q=q := by
  intro q hq
  have a:q≠L.core.poolWire 1285:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1285 (by omega))
  have b:q≠L.core.poolWire 1537:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1537 (by omega))
  exact Equiv.swap_apply_of_ne_of_ne a b

theorem run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (P : Program) (s : State) (m : List Bool)
    (hin : ∀q∈L.dialogPool,s.basis q=false)
    (hout : ∀q∈L.dialogPool,(run P m s).basis q=false) :
    run (renameProgram (swap L) P) m s=run P m s :=
  Square5Placement.pool_relabel_state_eq L (swap L) (pool L hw) (outside L hw) P s m ((regValue_zero _ _).mpr hin) ((regValue_zero _ _).mpr hout)

theorem square_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (baseState : BasisState) :
    Triple (PointDialogValues L X Y G baseState) (program L)
      (PointDialogValues L (-1-(X-(if G then Y*Y else 0))) Y G baseState) := by
  intro s m v
  have old:=OwnQ5Square.square_step L hw hn X Y G baseState s m v
  have eq:=Square5Placement.pool_relabel_state_eq L (swap L) (pool L hw) (outside L hw)
    (OwnQ5Square.program L) s m v.clean old.2.clean
  have eq2 : run (program L) m s = run (OwnQ5Square.program L) m s := by
    unfold program
    exact eq
  change _ ∧ _
  rw [eq2]
  exact old

theorem counts (L : ControlledPointLayout) :
    toffoliCount (program L)=toffoliCount (OwnQ5Square.program L) ∧
    measurementCount (program L)=measurementCount (OwnQ5Square.program L) := by
  unfold program
  exact renameProgram_counts (swap L) _

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  unfold program
  exact gatePhysical_rename (swap L) (swap L).injective _ (OwnQ5Square.physical L hw hn)

theorem slots (L : ControlledPointLayout) : Challenge.gateSlots (program L)=Challenge.gateSlots (OwnQ5Square.program L) := by
  unfold program
  exact Baselines.rename_gateSlots _ _

theorem retired_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1285 ∉ wires (program L) := by
  unfold program
  rw [renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have back : swap L (L.core.poolWire 1537)=L.core.poolWire 1285 := Equiv.swap_apply_right _ _
  have same : old=L.core.poolWire 1537 := (swap L).injective (e.trans back.symm)
  exact current_spare_free L hw hn (same ▸ used)

theorem support_transport (L : ControlledPointLayout) (S : Finset Wire)
    (old : wires (OwnQ5Square.program L)⊆S)
    (a : L.core.poolWire 1285∈S) (b : L.core.poolWire 1537∈S) : wires (program L)⊆S := by
  unfold program
  rw [renameProgram_support]
  intro q hq
  obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp hq
  by_cases x:w=L.core.poolWire 1285
  · subst w; simpa only [swap,Equiv.swap_apply_left] using b
  · by_cases y:w=L.core.poolWire 1537
    · subst w; simpa only [swap,Equiv.swap_apply_right] using a
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne x y] using old used
end ECDSAAdd.Entrant.Q6SquareHost

-- BEGIN ResourceAdapters
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6ResourceAdapters
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines

theorem arithEntryS_slots_eq (L : ControlledPointLayout) :
    gateSlots (OwnEntryFuseQ6.arithEntryS L)=gateSlots (EntryFuse.arithEntryS L) := by
  simpa only [OwnEntryFuseQ6.arithEntryS,EntryFuse.arithEntryS,rename_gateSlots] using
    OwnEntryFuseQ6.kernel5S_slots_eq

theorem division_counts_eq (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (OwnEntryFuseQ6.fusedDivisionF L k)=toffoliCount (EntryFuseFinite.fusedDivisionF L k) ∧
    measurementCount (OwnEntryFuseQ6.fusedDivisionF L k)=measurementCount (EntryFuseFinite.fusedDivisionF L k) := by
  have c:=OwnEntryFuseQ6.arithEntryS_counts_eq L
  simp only [OwnEntryFuseQ6.fusedDivisionF,EntryFuseFinite.fusedDivisionF,
    toffoliCount_append,measurementCount_append]
  exact ⟨congrArg (fun n => toffoliCount (EntryFuse.fusedY L k)+n) c.1,
    congrArg (fun n => measurementCount (EntryFuse.fusedY L k)+n) c.2⟩

theorem division_slots_eq (L : ControlledPointLayout) (k : Fp) :
    gateSlots (OwnEntryFuseQ6.fusedDivisionF L k)=gateSlots (EntryFuseFinite.fusedDivisionF L k) := by
  simp only [OwnEntryFuseQ6.fusedDivisionF,EntryFuseFinite.fusedDivisionF,gateSlots_append]
  exact congrArg (fun n => gateSlots (EntryFuse.fusedY L k)+n) (arithEntryS_slots_eq L)

theorem exit_counts_eq (L : ControlledPointLayout) :
    toffoliCount (OwnExitFuseQ6.arithExit L)=toffoliCount (OwnExitFuseQ5.arithExit L) ∧
    measurementCount (OwnExitFuseQ6.arithExit L)=measurementCount (OwnExitFuseQ5.arithExit L) :=
  OwnExitFuseQ6.arithExit_counts_eq L

theorem exit_slots_eq (L : ControlledPointLayout) :
    gateSlots (OwnExitFuseQ6.arithExit L)=gateSlots (OwnExitFuseQ5.arithExit L) := by
  simpa only [OwnExitFuseQ6.arithExit,OwnExitFuseQ5.arithExit,rename_gateSlots] using
    OwnExitFuseQ6.kernelS_slots_eq
end ECDSAAdd.Entrant.Q6ResourceAdapters
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6ComponentSupport
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires OwnEntryFuseQ6.arithEntryS OwnExitFuseQ6.arithExit fusedY

theorem division_support (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (OwnEntryFuseQ6.fusedDivisionF L k)⊆(OB5Support.sites L).toFinset := by
  simp only [OwnEntryFuseQ6.fusedDivisionF,wires_append,Finset.union_subset_iff]
  exact ⟨(fusedY_support L hw k).trans (finConst_sites L hw L.point.y (Or.inr rfl)),
    OwnEntryFuseQ6.arithEntryS_support L hw⟩

theorem division_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (OwnEntryFuseQ6.fusedDivisionF L k) := by
  simp only [OwnEntryFuseQ6.fusedDivisionF,gatePhysical_append]
  exact ⟨fusedY_physical L hw hn k,OwnEntryFuseQ6.arithEntryS_physical L hw hn⟩

theorem division_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (freeS : base 1541∉wires Q5FusionFields.hostField5S) (k : Nat)
    (hk : k∈[1800,766,765,767,770,1285]) (c : Fp) :
    L.core.poolWire k∉wires (OwnEntryFuseQ6.fusedDivisionF L c) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have old := ExitGenericQ5.constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [OwnEntryFuseQ6.fusedDivisionF,wires_append,Finset.mem_union,not_or]
  exact ⟨fun h=>old (fusedY_support L hw c h),Q6FusionOmissions.entry_avoids L hw hn freeS k hk⟩

theorem square_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (Q6SquareHost.program L)⊆(OB5Support.sites L).toFinset := by
  apply Q6SquareHost.support_transport L _
  · exact SquareOB5.support L hw hn
  all_goals
    apply List.mem_toFinset.mpr
    exact OB5Support.pool_in_sites L _ (OB5Support.pool_mem L _ (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))

theorem square_old_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770]) :
    L.core.poolWire k∉wires (SquareOB5.program L) := by
  have f:=ExitGenericQ5.generic_five_omissions L hw hn (OwnExitFuseQ5.arithExit L)
    (OwnExitFuseQ5.arithExit_support_selected L) 0 0 k hk
  intro used
  apply f
  simp only [ExitGenericQ5.generic,wires_append,Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr used))))

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) :
    L.core.poolWire k∉wires (Q6SquareHost.program L) := by
  by_cases same:k=1285
  · subst k;exact Q6SquareHost.retired_free L hw hn
  have prior : k∈[1800,766,765,767,770] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    rcases hk with h|h|h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact False.elim (same h)
  have bound:k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at prior
    rcases prior with rfl|rfl|rfl|rfl|rfl <;> omega
  have a:k≠1285 := same
  have b:k≠1537 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at prior
    rcases prior with rfl|rfl|rfl|rfl|rfl <;> decide
  have neA:L.core.poolWire k≠L.core.poolWire 1285:=fun h=>a (pool_inj L hw hn k 1285 (by omega) (by omega) h)
  have neB:L.core.poolWire k≠L.core.poolWire 1537:=fun h=>b (pool_inj L hw hn k 1537 (by omega) (by omega) h)
  exact OwnPlusHost.rename_avoid (Q6SquareHost.swap L) _ _
    (Equiv.swap_apply_of_ne_of_ne neA neB) (square_old_free L hw hn k prior)
end ECDSAAdd.Entrant.Q6ComponentSupport


-- Q6 INTEGRATION Generic.lean
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitGenericQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
  EntryFuseFinite ExitFusionResearch

/-- Source-only generic tail parameter; the actual shortened multiplier is supplied separately. -/
def generic (L : ControlledPointLayout) (D : Fp→Program) (S P : Program) (cx cy : Fp) : Program :=
  fastConstAdd L L.point.x (-cx) ++ D (-cy) ++
  S ++ fastConstRefl L (3*cx-1) ++
  P ++ exitY L cy ++ fastConstNeg L cx

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
variable (D : Fp→Program) (S P : Program) (halfCorrect : HalfMultiplyCorrect L P)
variable (divisionCorrect : ∀(X Y k : Fp)(G : Bool)(origin : BasisState),X≠0 →
  Triple (PointDialogValues L X Y G origin) (D k)
    (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin))
variable (squareCorrect : ∀(X Y : Fp)(G : Bool)(origin : BasisState),
  Triple (PointDialogValues L X Y G origin) S
    (PointDialogValues L (-1-(X-(if G then Y*Y else 0))) Y G origin))
include hw hn halfCorrect divisionCorrect squareCorrect
attribute [local irreducible] run arithS fastConstAdd fastConstNeg fastConstRefl exitY

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L D S P cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := fastStep_addX L hw hn X Y true origin (-cx)
  simp only [if_true,←sub_eq_add_neg] at h1
  have h2 := divisionCorrect
    (X-cx) Y (-cy) true origin (sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,←sub_eq_add_neg,ha] at h2
  have h3 := squareCorrect (X-cx) a true origin
  simp only [if_true] at h3
  have h4 := fastStep_refl L hw hn (-1-((X-cx)-a*a)) a true origin (3*cx-1)
  simp only [if_true] at h4
  have hd4 : 3*cx-1-(-1-((X-cx)-a*a))=d := by
    have e := hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [← e]; ring
  rw [hd4] at h4
  have h5 := fusedMultiply_step L hw hn P halfCorrect d a cy true origin hd
  simp only [if_true] at h5
  have h6 := fastStep_negX L hw hn d (a*d-cy) true origin cx
  simp only [if_true] at h6
  rw [show cx-d=genericX X Y cx cy by dsimp [d]; ring] at h6
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h5 h6
  have h := ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6
  simpa only [generic,fusedMultiply,List.append_assoc] using h

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L D S P cx cy)
      (PointDialogValues L X Y false origin) := by
  have h1 := fastStep_addX L hw hn X Y false origin (-cx)
  have h2 := divisionCorrect
    X Y (-cy) false origin hX
  have h3 := squareCorrect X (Y/X) false origin
  have h4 := fastStep_refl L hw hn (-1-X) (Y/X) false origin (3*cx-1)
  have h5 := fusedMultiply_step L hw hn P halfCorrect X (Y/X) cy false origin hX
  have h6 := fastStep_negX L hw hn X Y false origin cx
  have back : Y/X*X=Y := div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6
  rw [show -1-(-1-X)=X by ring] at h4
  rw [back] at h5
  have h := ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6
  simpa only [generic,fusedMultiply,List.append_assoc] using h
end Correct
end ECDSAAdd.Entrant.ExitGenericQ6


-- Q6 INTEGRATION Wrap.lean
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ExitGenericQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
  EntryFuseFinite ExitFusionResearch
attribute [local irreducible] run wires generic
def mid (L : ControlledPointLayout) (D : Fp→Program) (S P : Program) (cx cy : Fp) : Program :=
  clrF L ++ renameProgram (swapF L) (generic L D S P cx cy) ++ clrF L

def gen (L : ControlledPointLayout) (D : Fp→Program) (S P : Program) (cx cy : Fp) : Program :=
  zrep L ++ mid L D S P cx cy ++ zrep L

section WrapCorrect
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
variable (D : Fp→Program) (S P : Program) (halfCorrect : HalfMultiplyCorrect L P)
variable (divisionCorrect : ∀(X Y k : Fp)(G : Bool)(origin : BasisState),X≠0 →
  Triple (PointDialogValues L X Y G origin) (D k)
    (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin))
variable (squareCorrect : ∀(X Y : Fp)(G : Bool)(origin : BasisState),
  Triple (PointDialogValues L X Y G origin) S
    (PointDialogValues L (-1-(X-(if G then Y*Y else 0))) Y G origin))
include hw hn

theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L D S P cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L D S P cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L D S P cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


include halfCorrect divisionCorrect squareCorrect

theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L D S P cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midFFused_values L hw hn D S P cx cy 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn D S P halfCorrect divisionCorrect squareCorrect 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn D S P cx cy x y x y false s.basis true
        (fun base' => generic_false L hw hn D S P halfCorrect divisionCorrect squareCorrect x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn D S P cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn D S P halfCorrect divisionCorrect squareCorrect x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))


end WrapCorrect
end ECDSAAdd.Entrant.ExitGenericQ6


-- Q6 INTEGRATION Properties.lean
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ExitGenericQ6
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
  EntryFuseFinite ExitFusionResearch
attribute [local irreducible] wires run generic gen mid fastConstAdd fastConstNeg fastConstRefl exitY
  toffoliCount measurementCount EntryFuseFinite.fusedDivisionF SquareOB5.program OwnExitFuseQ5.arithExit

theorem add_palette (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (fastConstAdd L L.point.x k)⊆(L.core.generic::(L.recoveryConstant L.point.x).wires).toFinset := by
  simpa only [fastConstAdd] using FastConst.fastAdd_support
    (K:=L.recoveryConstant L.point.x) (g:=L.core.generic) SquareReduction.c k.val
    ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩
theorem refl_palette (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (fastConstRefl L k)⊆(L.core.generic::(L.recoveryConstant L.point.x).wires).toFinset := by
  simpa only [fastConstRefl] using FastConst.fastRefl_support
    (K:=L.recoveryConstant L.point.x) (g:=L.core.generic) p k.val
    ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩
theorem neg_palette (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (fastConstNeg L k)⊆(L.core.generic::(L.recoveryConstant L.point.x).wires).toFinset := by
  simpa only [fastConstNeg] using FastConst.fastNeg_support
    (K:=L.recoveryConstant L.point.x) (g:=L.core.generic) p k.val
    ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩

private theorem metric7_eq (metric : Program → Nat)
    (app : ∀a b,metric (a++b)=metric a+metric b)
    (a b b' c c' d e e' f g : Program)
    (hb : metric b=metric b') (hc : metric c=metric c') (he : metric e=metric e') :
    metric (a++b++c++d++e++f++g)=metric (a++b'++c'++d++e'++f++g) := by
  simp only [app]
  rw [hb,hc,he]

theorem generic_counts_eq (L : ControlledPointLayout) (D : Fp→Program) (S P : Program)
    (hD : ∀k,toffoliCount (D k)=toffoliCount (EntryFuseFinite.fusedDivisionF L k) ∧
      measurementCount (D k)=measurementCount (EntryFuseFinite.fusedDivisionF L k))
    (hS : toffoliCount S=toffoliCount (SquareOB5.program L) ∧
      measurementCount S=measurementCount (SquareOB5.program L))
    (hP : toffoliCount P=toffoliCount (OwnExitFuseQ5.arithExit L) ∧
      measurementCount P=measurementCount (OwnExitFuseQ5.arithExit L)) (cx cy : Fp) :
    toffoliCount (generic L D S P cx cy)=toffoliCount (OwnExitProducer.genericE L cx cy) ∧
    measurementCount (generic L D S P cx cy)=measurementCount (OwnExitProducer.genericE L cx cy) := by
  constructor
  · unfold generic OwnExitProducer.genericE ExitGenericQ5.generic
    exact metric7_eq toffoliCount toffoliCount_append
      (fastConstAdd L L.point.x (-cx)) (D (-cy)) (EntryFuseFinite.fusedDivisionF L (-cy))
      S (SquareOB5.program L) (fastConstRefl L (3*cx-1)) P (OwnExitFuseQ5.arithExit L)
      (exitY L cy) (fastConstNeg L cx) (hD (-cy)).1 hS.1 hP.1
  · unfold generic OwnExitProducer.genericE ExitGenericQ5.generic
    exact metric7_eq measurementCount measurementCount_append
      (fastConstAdd L L.point.x (-cx)) (D (-cy)) (EntryFuseFinite.fusedDivisionF L (-cy))
      S (SquareOB5.program L) (fastConstRefl L (3*cx-1)) P (OwnExitFuseQ5.arithExit L)
      (exitY L cy) (fastConstNeg L cx) (hD (-cy)).2 hS.2 hP.2


theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (D : Fp→Program) (S P : Program)
    (hD : ∀k,wires (D k)⊆(OB5Support.sites L).toFinset)
    (hS : wires S⊆(OB5Support.sites L).toFinset)
    (hP : wires P⊆(OB5Support.sites L).toFinset) (cx cy : Fp) :
    wires (generic L D S P cx cy)⊆(OB5Support.sites L).toFinset := by
  have ca : wires (fastConstAdd L L.point.x (-cx)) ⊆ (OB5Support.sites L).toFinset := (add_palette L hw (-cx)).trans
    (finConst_sites L hw L.point.x (Or.inl rfl))
  have cr : wires (fastConstRefl L (3*cx-1)) ⊆ (OB5Support.sites L).toFinset := (refl_palette L hw (3*cx-1)).trans
    (finConst_sites L hw L.point.x (Or.inl rfl))
  have cn : wires (fastConstNeg L cx) ⊆ (OB5Support.sites L).toFinset := (neg_palette L hw cx).trans
    (finConst_sites L hw L.point.x (Or.inl rfl))
  have ey := (exitY_support L hw cy).trans (finConst_sites L hw L.point.y (Or.inr rfl))
  simp only [generic,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨ca,hD (-cy)⟩,hS⟩,cr⟩,hP⟩,ey⟩,cn⟩

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp→Program) (S P : Program) (hD : ∀k,GatePhysical (D k))
    (hS : GatePhysical S) (hP : GatePhysical P) (cx cy : Fp) :
    GatePhysical (generic L D S P cx cy) := by
  have ca := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) SquareReduction.c (-cx).val
  have cr := FastConst.fastRefl_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p (3*cx-1).val
  have cn := FastConst.fastNeg_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p cx.val
  have ey := exitY_physical L hw hn cy
  simp only [generic,fastConstAdd,fastConstRefl,fastConstNeg,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨ca,hD (-cy)⟩,hS⟩,cr⟩,hP⟩,ey⟩,cn⟩

theorem generic_slots_eq (L : ControlledPointLayout) (D : Fp→Program) (S P : Program)
    (hD : ∀k,gateSlots (D k)=gateSlots (EntryFuseFinite.fusedDivisionF L k))
    (hS : gateSlots S=gateSlots (SquareOB5.program L))
    (hP : gateSlots P=gateSlots (OwnExitFuseQ5.arithExit L)) (cx cy : Fp) :
    gateSlots (generic L D S P cx cy)=gateSlots (OwnExitProducer.genericE L cx cy) := by
  unfold generic OwnExitProducer.genericE ExitGenericQ5.generic
  exact metric7_eq gateSlots gateSlots_append
    (fastConstAdd L L.point.x (-cx)) (D (-cy)) (EntryFuseFinite.fusedDivisionF L (-cy))
    S (SquareOB5.program L) (fastConstRefl L (3*cx-1)) P (OwnExitFuseQ5.arithExit L)
    (exitY L cy) (fastConstNeg L cx) (hD (-cy)) hS hP


theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp→Program) (S P : Program) (k : Nat) (hk : 515≤k ∧ k<2613)
    (hD : ∀c,L.core.poolWire k∉wires (D c))
    (hS : L.core.poolWire k∉wires S) (hP : L.core.poolWire k∉wires P)
    (cx cy : Fp) : L.core.poolWire k∉wires (generic L D S P cx cy) := by
  have x := ExitGenericQ5.constant_ports_avoid_large L hw hn k hk L.point.x (Or.inl rfl)
  have y := ExitGenericQ5.constant_ports_avoid_large L hw hn k hk L.point.y (Or.inr rfl)
  have ca := (add_palette L hw (-cx))
  have cr := (refl_palette L hw (3*cx-1))
  have cn := (neg_palette L hw cx)
  have ey := exitY_support L hw cy
  simp only [generic,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨fun h=>x (ca h),hD (-cy)⟩,hS⟩,fun h=>x (cr h)⟩,hP⟩,
    fun h=>y (ey h)⟩,fun h=>x (cn h)⟩

theorem gen_shape (L : ControlledPointLayout) (D : Fp→Program) (S P : Program) (cx cy : Fp) :
    gen L D S P cx cy=GenericQ5Geometry.wrapG L (generic L D S P cx cy) := by
  simp only [gen,mid,GenericQ5Geometry.wrapG]

theorem gen_counts_eq (L : ControlledPointLayout) (D : Fp→Program) (S P : Program)
    (hD : ∀k,toffoliCount (D k)=toffoliCount (EntryFuseFinite.fusedDivisionF L k) ∧
      measurementCount (D k)=measurementCount (EntryFuseFinite.fusedDivisionF L k))
    (hS : toffoliCount S=toffoliCount (SquareOB5.program L) ∧
      measurementCount S=measurementCount (SquareOB5.program L))
    (hP : toffoliCount P=toffoliCount (OwnExitFuseQ5.arithExit L) ∧
      measurementCount P=measurementCount (OwnExitFuseQ5.arithExit L)) (cx cy : Fp) :
    toffoliCount (gen L D S P cx cy)=toffoliCount (OwnExitProducer.genE L cx cy) ∧
    measurementCount (gen L D S P cx cy)=measurementCount (OwnExitProducer.genE L cx cy) := by
  have h:=generic_counts_eq L D S P hD hS hP cx cy
  dsimp only [OwnExitProducer.genericE] at h
  simp only [gen,mid,OwnExitProducer.genE,ExitGenericQ5.gen,ExitGenericQ5.mid,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  constructor <;> omega

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp→Program) (S P : Program) (hD : ∀k,GatePhysical (D k))
    (hS : GatePhysical S) (hP : GatePhysical P) (cx cy : Fp) :
    GatePhysical (gen L D S P cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have r:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (generic_physical L hw hn D S P hD hS hP cx cy)
  simp only [gen,mid,gatePhysical_append]
  exact ⟨⟨z,⟨c,r⟩,c⟩,z⟩

theorem gen_slots_eq (L : ControlledPointLayout) (D : Fp→Program) (S P : Program)
    (hD : ∀k,gateSlots (D k)=gateSlots (EntryFuseFinite.fusedDivisionF L k))
    (hS : gateSlots S=gateSlots (SquareOB5.program L))
    (hP : gateSlots P=gateSlots (OwnExitFuseQ5.arithExit L)) (cx cy : Fp) :
    gateSlots (gen L D S P cx cy)=gateSlots (OwnExitProducer.genE L cx cy) := by
  have h:=generic_slots_eq L D S P hD hS hP cx cy
  dsimp only [OwnExitProducer.genericE] at h
  simp only [gen,mid,OwnExitProducer.genE,ExitGenericQ5.gen,ExitGenericQ5.mid,
    gateSlots_append,Baselines.rename_gateSlots]
  omega
end ECDSAAdd.Entrant.ExitGenericQ6


-- Q6 INTEGRATION InventoryEight.lean
open ECDSAAdd ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Entrant.Q6Inventory
attribute [local irreducible] wires
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
open FiniteHostStack FiniteHostFusion

/-- A proof-only witness charges the eighth retired wire, then removes its one unit.
The witness is never part of the emitted circuit. -/
theorem qubits_eight (P : Program)
    (sub : ioWires ∪ wires P ⊆ (WrapperOB5.sites layout).toFinset)
    (free : ∀ k ∈ ([1400,1800,766,765,767,1540,770] : List Nat),
      layout.core.poolWire k ∉ wires P)
    (extra : layout.core.poolWire 1285 ∉ wires P) : qubits P ≤ 1593 := by
  let q := layout.core.poolWire 1285
  let witness : Program := [.X q] ++ P
  have qm : q ∈ (WrapperOB5.sites layout).toFinset := by
    apply List.mem_toFinset.mpr
    simp only [q,WrapperOB5.sites,List.mem_append,List.mem_singleton,
      wireBlock,List.mem_map,List.mem_range'_1]
    exact Or.inl (Or.inr ⟨1285,by omega,rfl⟩)
  have ww : wires witness = insert q (wires P) := by
    unfold witness
    rw [wires_append]
    simp only [wires,Instr.wires,Finset.union_empty,Finset.singleton_union]
  have ws : ioWires ∪ wires witness ⊆ (WrapperOB5.sites layout).toFinset := by
    rw [ww]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact sub (Finset.mem_union.mpr (Or.inl hx))
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact qm
      · exact sub (Finset.mem_union.mpr (Or.inr hx))
  have wf : ∀ k ∈ ([1400,1800,766,765,767,1540,770] : List Nat),
      layout.core.poolWire k ∉ wires witness := by
    intro k hk
    rw [ww]
    intro h
    rcases Finset.mem_insert.mp h with he | hp
    · have hkbound : k < 2613 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
      have kne : k ≠ 1285 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
      exact kne (pool_inj layout layout_widths layout_nodup k 1285 hkbound (by omega) he)
    · exact free k hk hp
  have bound := Q5FusionInventory.qubits_seven witness ws wf
  have fresh : q ∉ ioWires ∪ wires P := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact FiniteHostStack.io_avoids_pool 1285 (by omega) h
    · exact extra h
  have sets : ioWires ∪ wires witness = insert q (ioWires ∪ wires P) := by
    rw [ww,Finset.union_insert]
  change (ioWires ∪ wires witness).card ≤ 1594 at bound
  rw [sets,Finset.card_insert_of_notMem fresh] at bound
  change (ioWires ∪ wires P).card ≤ 1593
  omega
end ECDSAAdd.Entrant.Q6Inventory


-- Q6 INTEGRATION GenericGeometry6.lean
open ECDSAAdd ECDSAAdd.Entrant
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.GenericQ6Geometry
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
open FiniteHostStack FiniteHostFusion FiniteHostFive GenericQ5Geometry
 theorem edges_wrapG_qubits (G : Program)
    (hG : wires G⊆(OB5Support.sites layout).toFinset)
    (hFree : ∀k∈([1800,766,765,767,770] : List Nat),layout.core.poolWire k∉wires G)
    (extra : layout.core.poolWire 1285∉wires G)
    (C : Point) (cy : Fp) : qubits (Edges.wrapper layout C cy (wrapG layout G))≤1593 := by
  have supported := Edges.wrapper_support layout layout_widths layout_nodup C cy _
    (wrapG_sites layout layout_widths layout_nodup G hG)
  have sub := Finset.union_subset FiniteHostStack.io_support_original supported
  have edge (k : Nat) (hk : 515≤k ∧ k<2613)
      (old : layout.core.poolWire k∉wires (WrapperOB5.program layout C cy (wrapG layout G))) :
      layout.core.poolWire k∉wires (Edges.wrapper layout C cy (wrapG layout G)) := by
    intro h
    rcases Finset.mem_union.mp (Edges.wrapper_wires layout C cy _ h) with h|h
    · exact old h
    · exact Edges.small_away layout layout_widths layout_nodup k hk (Edges.extra_small layout layout_widths layout_nodup C h)
  have omitted (k : Nat) (hk : k∈([1800,766,765,767,770] : List Nat)) :
      layout.core.poolWire k∉wires (Edges.wrapper layout C cy (wrapG layout G)) := by
    have bounds : 515≤k ∧ k<2613 ∧ k≠684 ∧ k≠717 ∧ k≠1400 ∧ k≠1540 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl <;> omega
    apply edge k ⟨bounds.1,bounds.2.1⟩
    exact finWrapper_avoid layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩
      bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.2 _
      (wrapG_avoid_of_generic layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩ bounds.2.2.2.2.1 G (hFree k hk)) C cy
  apply Q6Inventory.qubits_eight _ sub
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · apply edge 1400 (by omega)
      exact finWrapper_avoid layout layout_widths layout_nodup 1400 (by omega) (by omega) (by omega) (by omega) _
        (spare_not_wrapG layout layout_widths layout_nodup G hG) C cy
    · exact omitted 1800 (by simp)
    · exact omitted 766 (by simp)
    · exact omitted 765 (by simp)
    · exact omitted 767 (by simp)
    · apply edge 1540 (by omega)
      exact finWrapper_avoid1540 layout layout_widths layout_nodup _ (wrapG_noDouble G hG) C cy
    · exact omitted 770 (by simp)
  · apply edge 1285 (by omega)
    exact finWrapper_avoid layout layout_widths layout_nodup 1285 (by omega)
      (by omega) (by omega) (by omega) _
      (wrapG_avoid_of_generic layout layout_widths layout_nodup 1285 (by omega)
        (by omega) G extra) C cy
end ECDSAAdd.Entrant.GenericQ6Geometry


-- Q6 INTEGRATION Producer.lean
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnQ6Producer
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run fastConstAdd fastConstNeg fastConstRefl ExitFusionResearch.exitY

def genericE (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ExitGenericQ6.generic L (OwnEntryFuseQ6.fusedDivisionF L) (Q6SquareHost.program L)
    (OwnExitFuseQ6.arithExit L) cx cy

def genE (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ExitGenericQ6.gen L (OwnEntryFuseQ6.fusedDivisionF L) (Q6SquareHost.program L)
    (OwnExitFuseQ6.arithExit L) cx cy

theorem genericE_counts_eq (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (genericE L cx cy)=toffoliCount (OwnExitProducer.genericE L cx cy) ∧
    measurementCount (genericE L cx cy)=measurementCount (OwnExitProducer.genericE L cx cy) :=
  ExitGenericQ6.generic_counts_eq L _ _ _ (Q6ResourceAdapters.division_counts_eq L)
    (Q6SquareHost.counts L) (Q6ResourceAdapters.exit_counts_eq L) cx cy

theorem genE_counts_eq (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (genE L cx cy)=toffoliCount (OwnExitProducer.genE L cx cy) ∧
    measurementCount (genE L cx cy)=measurementCount (OwnExitProducer.genE L cx cy) :=
  ExitGenericQ6.gen_counts_eq L _ _ _ (Q6ResourceAdapters.division_counts_eq L)
    (Q6SquareHost.counts L) (Q6ResourceAdapters.exit_counts_eq L) cx cy

theorem genericE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (genericE L cx cy)⊆(OB5Support.sites L).toFinset :=
  ExitGenericQ6.generic_sites L hw _ _ _ (Q6ComponentSupport.division_support L hw)
    (Q6ComponentSupport.square_support L hw hn) (OwnExitFuseQ6.arithExit_support L hw) cx cy

theorem genE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (genE L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [genE,ExitGenericQ6.gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (genericE_sites L hw hn cx cy)

theorem genE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    GatePhysical (genE L cx cy) :=
  ExitGenericQ6.gen_physical L hw hn _ _ _ (Q6ComponentSupport.division_physical L hw hn)
    (Q6SquareHost.physical L hw hn) (OwnExitFuseQ6.arithExit_physical L hw hn) cx cy

theorem genE_slots_eq (L : ControlledPointLayout) (cx cy : Fp) :
    gateSlots (genE L cx cy)=gateSlots (OwnExitProducer.genE L cx cy) :=
  ExitGenericQ6.gen_slots_eq L _ _ _ (Q6ResourceAdapters.division_slots_eq L)
    (Q6SquareHost.slots L) (Q6ResourceAdapters.exit_slots_eq L) cx cy

theorem genericE_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) (cx cy : Fp) :
    L.core.poolWire k∉wires (genericE L cx cy) := by
  have bounds:515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  exact ExitGenericQ6.generic_free L hw hn _ _ _ k bounds
    (Q6ComponentSupport.division_free L hw hn entryFree k hk)
    (Q6ComponentSupport.square_free L hw hn k hk)
    (Q6FusionOmissions.exit_avoids L hw hn exitFree k hk) cx cy

theorem genE_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base)) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (genE L cx cy) :=
  ExitGenericQ6.genFFused_ok L hw hn _ _ _
    (OwnExitFuseQ6.arithExit_correct exitFree L hw hn)
    (OwnEntryFuseQ6.fusedDivisionF_step entryFree L hw hn logicalND hlo logicalAway logicalReplay)
    (Q6SquareHost.square_step L hw hn) hc
end ECDSAAdd.Entrant.OwnQ6Producer


-- Q6 INTEGRATION Final.lean
namespace ECDSAAdd.Entrant.OwnQ6Producer
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite

theorem genE_qubits1593 (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (genE layout cx cy))≤1593 := by
  rw [genE,ExitGenericQ6.gen_shape]
  apply GenericQ6Geometry.edges_wrapG_qubits _ (genericE_sites layout layout_widths layout_nodup cx cy)
  · intro k hk
    exact genericE_free layout layout_widths layout_nodup OwnQ6Actual.entry_selected_free
      OwnQ6Actual.exit_selected_free k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with h|h|h|h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) cx cy
  · exact genericE_free layout layout_widths layout_nodup OwnQ6Actual.entry_selected_free
      OwnQ6Actual.exit_selected_free 1285 (by simp) cx cy
end ECDSAAdd.Entrant.OwnQ6Producer

namespace ECDSAAdd.Entrant.All12ParentCertificate
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (OwnQ6Producer.genE layout cx cy)
def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2155162,1500875,1593,50000004⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have cfg:=MappedCompressed.LaneA.laneLogical_config
    have above:History5.HistoryAbove MappedCompressed.base:=by intro j hj;simp [MappedCompressed.base]
    have hG:=OwnQ6Producer.genE_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (OwnQ6Producer.genE_ok layout layout_widths layout_nodup OwnQ6Actual.entry_selected_free
          OwnQ6Actual.exit_selected_free cfg.1 above cfg.2.1 cfg.2.2 hc) hG)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ hG).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2155162 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have h:=(Edges.wrapper_counts layout layout_widths (OwnQ6Producer.genE layout cx cy) hc).1
    have g:=(SelGeneric5.program_counts layout layout_widths cx cy).1
    have gf:=(genF_counts layout layout_widths cx cy).1
    have gd:=(genFFused_counts_diff layout layout_widths cx cy).1
    have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).1
    have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).1
    change toffoliCount (Edges.wrapper layout (.some hc) cy (OwnQ6Producer.genE layout cx cy))≤2155162
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1500875 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have h:=(Edges.wrapper_counts layout layout_widths (OwnQ6Producer.genE layout cx cy) hc).2
    have g:=(SelGeneric5.program_counts layout layout_widths cx cy).2
    have gf:=(genF_counts layout layout_widths cx cy).2
    have gd:=(genFFused_counts_diff layout layout_widths cx cy).2
    have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).2
    have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).2
    change measurementCount (Edges.wrapper layout (.some hc) cy (OwnQ6Producer.genE layout cx cy))≤1500875
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1593 := by
  cases C with
  | zero => change qubits []≤1593;rw [qubits_empty];decide
  | @some cx cy hc => exact OwnQ6Producer.genE_qubits1593 (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (OwnQ6Producer.genE_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50000004 := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc =>
    have h:=Edges.wrapper_slots layout layout_widths (.some hc) cy (OwnQ6Producer.genE layout cx cy)
    have g:=OwnExitProducer.genE_gateSlots_le layout layout_widths layout_nodup cx cy
    rw [←OwnQ6Producer.genE_slots_eq layout cx cy] at g
    change gateSlots (Edges.wrapper layout (.some hc) cy (OwnQ6Producer.genE layout cx cy))≤_
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1500875
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1593
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50000004
    rw [normalize_slots];exact program_gateSlots C
end ECDSAAdd.Entrant.All12ParentCertificate


namespace ECDSAAdd.Entrant
def program := All12ParentCertificate.program
def entry := All12ParentCertificate.entry
def bounds := All12ParentCertificate.bounds
theorem certificate : Challenge.Certificate entry bounds := All12ParentCertificate.certificate
end ECDSAAdd.Entrant
