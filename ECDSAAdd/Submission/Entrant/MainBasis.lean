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
def bounds : Challenge.Bounds := ⟨2155482,1501199,1593,50000004⟩

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

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2155482 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have h:=(Edges.wrapper_counts layout layout_widths (OwnQ6Producer.genE layout cx cy) hc).1
    have g:=(SelGeneric5.program_counts layout layout_widths cx cy).1
    have gf:=(genF_counts layout layout_widths cx cy).1
    have gd:=(genFFused_counts_diff layout layout_widths cx cy).1
    have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).1
    have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).1
    change toffoliCount (Edges.wrapper layout (.some hc) cy (OwnQ6Producer.genE layout cx cy))≤2155482
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1501199 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have h:=(Edges.wrapper_counts layout layout_widths (OwnQ6Producer.genE layout cx cy) hc).2
    have g:=(SelGeneric5.program_counts layout layout_widths cx cy).2
    have gf:=(genF_counts layout layout_widths cx cy).2
    have gd:=(genFFused_counts_diff layout layout_widths cx cy).2
    have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).2
    have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).2
    change measurementCount (Edges.wrapper layout (.some hc) cy (OwnQ6Producer.genE layout cx cy))≤1501199
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
    change measurementCount (normalizeProgram (program C))≤1501199
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1593
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50000004
    rw [normalize_slots];exact program_gateSlots C
end ECDSAAdd.Entrant.All12ParentCertificate


-- ALL12 COMPONENT All12Primitive

section
-- ===== SquareAccK =====

/-! The accumulated streamed square with all three leaves computed by one
Karatsuba level (`withLowK`), the sum and cross registers borrowed from `ext`. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.OwnAll12Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

structure ExtOK (L : CuccaroStreamedSquareWideLayout) (control : Wire) (ext : List Wire) : Prop where
  nodup : ext.Nodup
  away : ∀q∈ext,q∉control::L.wires
  len : 300≤ext.length

theorem ext_out (L : CuccaroStreamedSquareWideLayout) (control : Wire) (ext : List Wire)
    (he : ExtOK L control ext) (q : Wire) (hq : q∈ext) : q∉L.core.out := fun h =>
  he.away q hq (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])

theorem sum_in (L : CuccaroStreamedSquareWideLayout) (control : Wire) (q : Wire) (h : q∈L.core.sum) :
    q∈control::L.wires := by
  simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h
  · simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
      List.mem_of_mem_drop (List.mem_of_mem_take h)]
  · simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]

theorem withMixedK_contribution (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (hs2 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (orientation : Bool) (items : List MixItem)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (O P V : Nat) (hO : O<SquareReduction.p)
    (ho : regValue L.core.out s.basis=O)
    (hp : P=(if s.basis control then regValue src s.basis else 0)^2)
    (whole : ∀t : BasisState,regValue dst t=P → (∀q,q∉dst → t q=s.basis q) → regValue L.core.product t=P)
    (views : ∀t : BasisState,regValue L.core.product t=P → ∀i∈items,MixView L t i)
    (delta : ZMod SquareReduction.p)
    (payload : ∀t : BasisState,regValue L.core.product t=P → mixSignedSum t items=delta)
    (hV : V<SquareReduction.p)
    (target : measuredOrientationCast (mixFinal orientation items) V=
      measuredOrientationCast orientation O+delta)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) (hst : ∀i∈items,MixStatic L i) :
    (run (withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).phase=s.phase ∧
    regValue L.core.out (run (withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (mixFoldsQ L orientation items) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (mixFoldsQ_support L hw nd control orientation items hst hw'))
  apply withLowK2_correct L hw control hn src dst hs hd hs2 hsmax hlen ext he.nodup he.away he.len
    (mixFoldsQ L orientation items) hbody s records hc hzero hz V
  intro t m dstValue same
  have pv : regValue L.core.product t.basis=P := whole t.basis (by simpa [hp] using dstValue) same
  have clean := L.measured_product_frame_clean nd dst hd s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉dst := by
    intro bad
    have dis := L.product_out_disjoint nd
    have pos := List.count_pos_iff.mpr bad
    have bound := hd q
    have product : q∈L.core.product := List.count_pos_iff.mp (by omega)
    exact List.disjoint_left.mp dis product hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have initial : SquareFrame L.core.out t.basis O t.basis := ⟨outO,fun _ _ => rfl⟩
  have folded := mixFoldsQ_frame L hw nd t.basis clean orientation O hO items (views t.basis pv) t m initial
  have cast := mixValue_cast t.basis orientation O items hO
  rw [payload t.basis pv] at cast
  have result : mixValue t.basis orientation O items=V :=
    measuredOrientationCast_injective _ _ _ (mixValue_lt _ _ _ _ hO) hV (cast.trans target.symm)
  exact ⟨folded.1,folded.2.1.trans result,folded.2.2⟩


/-- Branch C forms `high ← high + low` with the measured in-place adder (n-1
Toffolis) instead of the Cuccaro ripple (2n); the clean work register holds
its carries. The sum is removed by the measured in-place subtractor. -/
def sumSrc (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.low++[L.core.pad.getD 0 0]
def sumBank (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 128
def gPrep (L : CuccaroStreamedSquareWideLayout) : Program :=
  addInPlace (sumSrc L) L.core.sum (sumBank L) L.core.cin
def gClear (L : CuccaroStreamedSquareWideLayout) : Program :=
  subInPlace (sumSrc L) L.core.sum (sumBank L) L.core.cin


theorem sum_lengths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (sumSrc L).length=129 ∧ L.core.sum.length=129 ∧ (sumBank L).length=128 := by
  refine ⟨?_,L.core.sum_length hw.core,?_⟩
  · simp [sumSrc,L.core.low_length hw.core]
  · simp [sumBank,hw.core.work]

theorem sumPad_mem (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.core.pad.getD 0 0∈L.core.pad := by
  have h : 0<L.core.pad.length := by rw [hw.core.pad]; omega
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem sum_nodup (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    (L.core.cin::(sumSrc L++L.core.sum++sumBank L)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hnd q
  have hlo := (List.take_sublist 128 L.core.y).count_le q
  have hhi1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
  have hhi2 := (List.drop_sublist 128 L.core.y).count_le q
  have hsplit := congrArg (List.count q) (List.take_append_drop 128 L.core.y)
  have hbit := (List.singleton_sublist.mpr (sumPad_mem L hw)).count_le q
  have hwk := (List.take_sublist 128 L.core.work).count_le q
  simp only [List.count_cons,List.count_nil,Nat.add_zero] at hbit
  simp only [List.count_append] at hsplit
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,sumSrc,sumBank,
    CuccaroStreamedSquareLayout.low,CuccaroStreamedSquareLayout.high,
    CuccaroStreamedSquareLayout.sum,List.count_append,List.count_cons,
    List.count_nil] at h ⊢
  omega

theorem sumSrc_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (base : BasisState) (A : Nat)
    (hA : regValue L.core.low base=A) (hpad : regValue L.core.pad base=0) :
    regValue (sumSrc L) base=A := by
  have bit0 : base (L.core.pad.getD 0 0)=false :=
    (regValue_zero _ _).mp hpad _ (sumPad_mem L hw)
  rw [sumSrc,regValue_append,hA]
  have hz : regValue [L.core.pad.getD 0 0] base=0 := by
    change (if base (L.core.pad.getD 0 0) then 1 else 0)=0
    rw [bit0]
    rfl
  rw [hz,Nat.mul_zero,Nat.add_zero]

theorem sumBank_zero (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (hwork : regValue L.core.work base=0) : regValue (sumBank L) base=0 :=
  (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hwork q (List.mem_of_mem_take hq))

theorem gPrep_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B : Nat)
    (hA : regValue L.core.low base=A) (hbound : A+B<2^129) (hpad : regValue L.core.pad base=0)
    (hcin : base L.core.cin=false) (hwork : regValue L.core.work base=0) :
    Triple (SquareFrame L.core.sum base B) (gPrep L)
      (SquareFrame L.core.sum base (A+B)) := by
  have lens := sum_lengths L hw
  have add := addInPlace_cin_frame L.core.cin (sumSrc L) L.core.sum (sumBank L)
    (sum_nodup L hw hnd) (lens.1.trans lens.2.1.symm) (by rw [lens.2.2,lens.2.1]) base false hcin
    (sumBank_zero L base hwork) B
  have val : (B+regValue (sumSrc L) base+false.toNat)%2^L.core.sum.length=A+B := by
    rw [sumSrc_value L hw base A hA hpad,lens.2.1]
    simp only [Bool.toNat_false,Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega),Nat.add_comm]
  rw [val] at add
  exact add

theorem gClear_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B : Nat)
    (hA : regValue L.core.low base=A) (hbound : A+B<2^129) (hpad : regValue L.core.pad base=0)
    (hcin : base L.core.cin=false) (hwork : regValue L.core.work base=0) :
    Triple (SquareFrame L.core.sum base (A+B)) (gClear L)
      (SquareFrame L.core.sum base B) := by
  have lens := sum_lengths L hw
  have nd := sum_nodup L hw hnd
  have dis (w : Wire) (hw' : w∈L.core.cin::(sumSrc L++sumBank L)) : w∉L.core.sum := by
    intro hdw
    have hn := List.nodup_iff_count.mp nd w
    have h1 := List.count_pos_iff.mpr hw'
    have h2 := List.count_pos_iff.mpr hdw
    simp only [List.count_cons,List.count_append] at hn h1
    omega
  intro s m h
  unfold gClear
  have sv : regValue (sumSrc L) s.basis=A :=
    (regValue_congr _ _ _ (fun w hw' => h.2 w (dis w (by simp [hw'])))).trans
      (sumSrc_value L hw base A hA hpad)
  have kv : regValue (sumBank L) s.basis=0 :=
    (regValue_congr _ _ _ (fun w hw' => h.2 w (dis w (by simp [hw'])))).trans (sumBank_zero L base hwork)
  have cv : s.basis L.core.cin=false := (h.2 _ (dis _ (by simp))).trans hcin
  have hx : (sumSrc L).length=L.core.sum.length := lens.1.trans lens.2.1.symm
  have hc : (sumBank L).length+1=L.core.sum.length := by rw [lens.2.2,lens.2.1]
  have spec := subInPlace_spec (sumSrc L) L.core.sum (sumBank L) L.core.cin nd hx hc A (A+B) s m
    ⟨⟨⟨sv,h.1⟩,cv⟩,kv⟩
  have hv : regValue L.core.sum (run (subInPlace (sumSrc L) L.core.sum (sumBank L) L.core.cin) m s).basis=
      (A+B+2^L.core.sum.length-A)%2^L.core.sum.length := spec.2.1.1.2
  refine ⟨spec.1,?_,?_⟩
  · rw [hv,lens.2.1,show A+B+2^129-A=B+2^129 by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · intro w hw'
    exact (subInPlace_frame (sumSrc L) L.core.sum (sumBank L) L.core.cin nd hx hc s m cv kv w hw').trans
      (h.2 w hw')

theorem gSum_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (toffoliCount (gPrep L)=128 ∧ measurementCount (gPrep L)=128) ∧
    (toffoliCount (gClear L)=128 ∧ measurementCount (gClear L)=128) := by
  have lens := sum_lengths L hw
  have hx : (sumSrc L).length=L.core.sum.length := lens.1.trans lens.2.1.symm
  have hc : (sumBank L).length+1=L.core.sum.length := by rw [lens.2.2,lens.2.1]
  have a := addInPlace_counts (sumSrc L) L.core.sum (sumBank L) L.core.cin hx hc
  have b := subInPlace_counts (sumSrc L) L.core.sum (sumBank L) L.core.cin hx hc
  rw [lens.2.1] at a b
  exact ⟨a,b⟩

theorem gSum_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    ECDSAAdd.wires (gPrep L)⊆(control::L.wires).toFinset ∧
    ECDSAAdd.wires (gClear L)⊆(control::L.wires).toFinset := by
  have lens := sum_lengths L hw
  have hx : (sumSrc L).length=L.core.sum.length := lens.1.trans lens.2.1.symm
  have hc : (sumBank L).length+1=L.core.sum.length := by rw [lens.2.2,lens.2.1]
  have sub : (L.core.cin::(sumSrc L++L.core.sum++sumBank L)).toFinset⊆(control::L.wires).toFinset := by
    intro q hq
    have pad := sumPad_mem L hw
    have inW : q∈L.wires → q∈(control::L.wires).toFinset := fun h => by simp [h]
    apply inW
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc,
      sumSrc,sumBank,CuccaroStreamedSquareLayout.sum] at hq
    rcases hq with h|h|h|h|h|h
    · subst h; simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
    · have hy : q∈L.core.y := List.mem_of_mem_take h
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hy]
    · subst h
      simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_append,
        pad,true_or,or_true]
    · have hy : q∈L.core.y := List.mem_of_mem_drop (List.mem_of_mem_take h)
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hy]
    · subst h; simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
    · have hk : q∈L.core.work := List.mem_of_mem_take h
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hk]
  exact ⟨(addInPlace_wires _ _ _ _ hx hc).trans_subset sub,(subInPlace_wires _ _ _ _ hx hc).trans_subset sub⟩

theorem gSum_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    GatePhysical (gPrep L) ∧ GatePhysical (gClear L) := by
  have nd := sum_nodup L hw hnd
  exact ⟨addInPlace_physical _ _ _ _ nd,subInPlace_physical _ _ _ _ nd⟩

theorem gSum_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (gPrep L)≤12*129 ∧ Challenge.gateSlots (gClear L)≤12*129+2*129 := by
  have lens := sum_lengths L hw
  have a := Baselines.addInPlace_gateSlots_le (sumSrc L) L.core.sum (sumBank L) L.core.cin
  have b := Baselines.subInPlace_gateSlots_le (sumSrc L) L.core.sum (sumBank L) L.core.cin
  rw [lens.1] at a b
  rw [lens.2.1] at b
  exact ⟨a,b⟩



/-- Fold schedules ordered so the output orientation flips as often as possible;
every flip uses the comparison-free reflected core of `QFold`. -/
def accAMixQ (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (rot128F L),.inl (negP L),.inr ⟨false,[],earlyHTerms (L.core.product.drop 128),earlyHTerms (L.core.product.drop 128)⟩]
def accBMixQ (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (negP L),.inl (rot128F L),.inl (rotC L true 4),.inl (rotC L false 6),
    .inl (rotC L true 10),.inr ⟨false,preW L,termsB L,sortedItems false (accBRaw L)⟩,.inl (rotC L true 32)]

theorem accAMixQ_mem (L : CuccaroStreamedSquareWideLayout) (i : MixItem) (h : i∈accAMixQ L) : i∈accAMix L := by
  simp only [accAMixQ,accAMix,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; tauto
theorem accBMixQ_mem (L : CuccaroStreamedSquareWideLayout) (i : MixItem) (h : i∈accBMixQ L) : i∈accBMix L := by
  simp only [accBMixQ,accBMix,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; tauto
theorem accAMixQ_sum (L : CuccaroStreamedSquareWideLayout) (t : BasisState) :
    mixSignedSum t (accAMixQ L)=mixSignedSum t (accAMix L) := by
  simp only [accAMixQ,accAMix,mixSignedSum]; ring
theorem accBMixQ_sum (L : CuccaroStreamedSquareWideLayout) (t : BasisState) :
    mixSignedSum t (accBMixQ L)=mixSignedSum t (accBMix L) := by
  simp only [accBMixQ,accBMix,mixSignedSum]; ring
theorem accQ_orientations (L : CuccaroStreamedSquareWideLayout) :
    mixFinal true (accAMixQ L)=false ∧ mixFinal false (accBMixQ L)=true ∧
    mixFinal false (accCMix L)=true := by
  simp [mixFinal,mixNeg,accAMixQ,accBMixQ,accCMix,rot128F,negP,negRot,rotC]
theorem accQ_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀i∈accAMixQ L,MixStatic L i) ∧ (∀i∈accBMixQ L,MixStatic L i) :=
  ⟨fun i hi => (acc_static L hw).1 i (accAMixQ_mem L i hi),
    fun i hi => (acc_static L hw).2.1 i (accBMixQ_mem L i hi)⟩
theorem accQ_item_prices (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (mixFoldsQT true (accAMixQ L)=3089 ∧ mixFoldsQM true (accAMixQ L)=3092) ∧
    (mixFoldsQT false (accBMixQ L)=7049 ∧ mixFoldsQM false (accBMixQ L)=7056) ∧
    (mixFoldsQT false (accCMix L)=2646 ∧ mixFoldsQM false (accCMix L)=2647) := by
  norm_num [mixFoldsQT,mixFoldsQM,mixNeg,accAMixQ,accBMixQ,accCMix,rot128F,negP,negRot,rotF,rotC,posTop,
    accARaw,accBRaw,accCRaw,sortedItems,nafMinusOneItems,List.filter_cons,Acc.buildT,Acc.sbuildT,preW,termsB,
    accPrice,accPriceQ,earlyHTerms,Acc.earlyTerm,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,hw.core.product,hiReg]
  all_goals (try rw [if_neg (List.cons_ne_nil _ _)])
  all_goals norm_num

def resAQ (P O : Nat) : Nat :=
  ofCast false (measuredOrientationCast true O+((P : ZMod SquareReduction.p)*2^128-P))
def resBQ (P O : Nat) : Nat :=
  ofCast true (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-SquareReduction.c*P))

theorem acbQ_complete_exact (enabled : Bool) (A B O : Nat) :
    resBQ ((if enabled then B else 0)^2)
      (resAQ ((if enabled then A else 0)^2) (resC ((if enabled then A+B else 0)^2) O))=
      SquareReduction.p-1-subModValue (if enabled then (A+2^128*B)^2 else 0) O := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resC PC O
  let OA := resAQ PA OC
  let OB := resBQ PB OA
  have ec : measuredOrientationCast true OC=measuredOrientationCast false O+(-(PC : ZMod SquareReduction.p)*2^128) :=
    cast_ofCast _ _
  have ea : measuredOrientationCast false OA=measuredOrientationCast true OC+((PA : ZMod SquareReduction.p)*2^128-PA) :=
    cast_ofCast _ _
  have eb : measuredOrientationCast true OB=measuredOrientationCast false OA+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB) := cast_ofCast _ _
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have obBound : OB<SquareReduction.p := ofCast_lt _ _
  have cast : (OB : ZMod SquareReduction.p)=
      -1-(subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    rw [subModValue_cast]
    linear_combination -eb-ec-ea-identity
  have targetBound : subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p :=
    Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have hp0 : ((SquareReduction.p : Nat) : ZMod SquareReduction.p)=0 := ZMod.natCast_self _
  have e : ((SquareReduction.p-1-subModValue (if enabled then (A+2^128*B)^2 else 0) O : Nat) : ZMod SquareReduction.p)=
      -1-(subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]),Nat.cast_one,hp0]
    ring
  have value := congrArg ZMod.val (cast.trans e.symm)
  have lt2 : SquareReduction.p-1-subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p := by omega
  simpa only [ZMod.val_natCast_of_lt obBound,ZMod.val_natCast_of_lt lt2] using value

/-! Branch C's accumulator is folded positively. A controlled complement
`acc ← acc XOR g·(2^163-1)` turns the negative item `-acc` into the positive item
`2^163-1-acc` plus the constant `g·(2^163-1)`, so both C items switch orientation
(comparison-free `Q` folds) and the square ends in the plain orientation. The
constant is absorbed by the following `3cx` correction. -/
def cFlipK : Nat := 2^163-1

theorem xorConstant_ones (r : List Wire) : xorConstant r (2^r.length-1)=notRegister r := by
  induction r with
  | nil => rfl
  | cons w ws ih =>
    have hp : 0<2^ws.length := Nat.two_pow_pos _
    have e : 2^(ws.length+1)=2*2^ws.length := by rw [Nat.pow_succ]; ring
    have h1 : (2^(ws.length+1)-1)%2=1 := by rw [e]; omega
    have h2 : (2^(ws.length+1)-1)/2=2^ws.length-1 := by rw [e]; omega
    simp only [List.length_cons,xorConstant,h1,if_true,h2,ih,notRegister,List.map_cons]
    rfl

theorem accReg_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) : (accReg L).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hn q
  have e1 : (L.core.work.take 163).count q+(L.core.work.drop 163).count q=L.core.work.count q := by
    rw [←List.count_append,List.take_append_drop]
  simp only [accReg]
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at h
  omega

theorem accReg_in (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq : q∈accReg L) : q∈L.wires := by
  have w := accReg_work L q hq
  simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,w]

theorem flip_run (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉accReg L) (s : State) (m : List Bool) :
    (run (maskedConstant g (accReg L) cFlipK) m s).phase=s.phase ∧
    (∀q,q∉accReg L → (run (maskedConstant g (accReg L) cFlipK) m s).basis q=s.basis q) ∧
    regValue (accReg L) (run (maskedConstant g (accReg L) cFlipK) m s).basis=
      (if s.basis g then cFlipK-regValue (accReg L) s.basis else regValue (accReg L) s.basis) := by
  have len := (acc_lengths L hw).1
  have nd := accReg_nodup L hn
  rw [maskedConstant_run g _ _ hg]
  cases hs : s.basis g
  · simp
  · have e : cFlipK=2^(accReg L).length-1 := by rw [len]; rfl
    simp only [if_true]
    rw [e,xorConstant_ones,notRegister_correct _ nd]
    refine ⟨rfl,?_,?_⟩
    · intro q hq; simp [hq]
    · change regValue (accReg L) (fun w => if w∈accReg L then !s.basis w else s.basis w)=_
      rw [regValue_congr (accReg L) _ (fun w => !s.basis w) (by intro w hw; simp [hw]),regValue_complement]

def accFoldQF (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) : Program :=
  fillIn L a++(maskedConstant g (accReg L) cFlipK++(qprog L.measuredCore SquareReduction.p++
    (maskedConstant g (accReg L) cFlipK++fillOut L a)))

theorem accFoldQF_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (g : Wire) (hg : g∉L.wires) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQF L g a)
      (SquareFrame L.core.out base (((if base g then cFlipK-Acc.accVal base 0 a.spec else Acc.accVal base 0 a.spec)+
        (SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have gAcc : g∉accReg L := fun h => hg (accReg_in L g h)
  have gOut : g∉L.core.out := fun h => hg (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have hAK : A≤cFlipK := by unfold cFlipK; omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^163 := by
    simp only [A']; split
    · unfold cFlipK; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillIn_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQF,run_append,run_append,run_append,run_append]
  let mb := measurementCount (fillIn L a)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprog L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (fillIn L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u1.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using accU1
  have outU : regValue L.core.out u1.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A'<SquareReduction.p := lt_of_lt_of_le hA' (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u1.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correct L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprog L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis else regValue (accReg L) v.basis) at fl2
  rw [gV,accV] at fl2
  have back : (if base g then cFlipK-A' else A')=A := by
    simp only [A']
    cases base g
    · simp
    · simp only [if_true]; omega
  rw [back] at fl2
  let base2 : BasisState := fun q => if q∈L.core.out then v1.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have frame2 : SquareFrame (accReg L) base2 A v1.basis := by
    refine ⟨fl2.2.2,?_⟩
    intro q hq
    by_cases ho : q∈L.core.out
    · simp [base2,ho]
    · rw [b2off q ho,fl2.2.1 q hq,ek.2.2 q ho,fl.2.1 q hq]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := fillOut_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (fillOut L a) (m3.drop mc) v1).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq,fl2.2.1 q na]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq

theorem accFoldQF_counts (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) :
    toffoliCount (accFoldQF L g a)=toffoliCount (accFoldQ L a) ∧
    measurementCount (accFoldQF L g a)=measurementCount (accFoldQ L a) := by
  have k := maskedConstant_counts g (accReg L) cFlipK
  simp only [accFoldQF,accFoldQ,toffoliCount_append,measurementCount_append,k.1,k.2]
  constructor <;> omega

theorem accFoldQF_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    ECDSAAdd.wires (accFoldQF L g a)⊆(g::L.wires).toFinset := by
  have full := accFoldQ_support L hw hn g a cnt ok cntP okP
  simp only [accFoldQ,wires_append,Finset.union_subset_iff] at full
  have mc : ECDSAAdd.wires (maskedConstant g (accReg L) cFlipK)⊆(g::L.wires).toFinset := by
    refine (maskedConstant_wires_subset _ _ _).trans ?_
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
    rcases hq with h|h
    · exact Or.inl h
    · exact Or.inr (accReg_in L q h)
  simp only [accFoldQF,wires_append,Finset.union_subset_iff]
  exact ⟨full.1.1,mc,full.1.2,mc,full.2⟩

theorem accFoldQF_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQF L g a) := by
  have full := accFoldQ_physical L hw hn a cnt ok cntP okP
  simp only [accFoldQ,gatePhysical_append] at full
  have mc := maskedConstant_physical g (accReg L) cFlipK (fun h => hg (accReg_in L g h))
  simp only [accFoldQF,gatePhysical_append]
  exact ⟨full.1.1,mc,full.1.2,mc,full.2⟩

theorem accFoldQF_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    Challenge.gateSlots (accFoldQF L g a)≤
      2*(a.terms.length*(14*163))+4*(a.pre.length*(14*33))+(67*256+41)+7000+2*163 := by
  have full := accFoldQ_gateSlots L hw a ok okP
  have mc := Baselines.maskedConstant_gateSlots_le g (accReg L) cFlipK
  rw [(acc_lengths L hw).1] at mc
  simp only [accFoldQ,Challenge.gateSlots_append] at full
  simp only [accFoldQF,Challenge.gateSlots_append]
  omega

def accCItem (L : CuccaroStreamedSquareWideLayout) : AccItem :=
  ⟨true,[],earlyHTerms (L.core.product.drop 128)++[posTop L],earlyHTerms (L.core.product.drop 128)++[posTop L]⟩

theorem accCMix_eq (L : CuccaroStreamedSquareWideLayout) : accCMix L=[.inl (negRot L),.inr (accCItem L)] := rfl

/-- Branch C body: `negRot` by the switching fold, then the complemented accumulator, also switching. -/
def bodyC (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  mixFoldsQ L false [.inl (negRot L)]++accFoldQF L g (accCItem L)

theorem bodyC_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀i∈[(.inl (negRot L) : MixItem)],MixStatic L i) ∧ MixStatic L (.inr (accCItem L)) := by
  have st := (acc_static L hw).2.2
  rw [accCMix_eq] at st
  exact ⟨fun i hi => st i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; exact Or.inl hi),
    st _ (by simp)⟩

theorem bodyC_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (bodyC L g)=2390 ∧ measurementCount (bodyC L g)=2392 := by
  have st := bodyC_static L hw
  have nR : (negRot L).negative=true := rfl
  have cR : (negRot L).canonical=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have f := mixFoldsQ_counts L hw false _ st.1
  have f1 : mixFoldsQT false [(.inl (negRot L) : MixItem)]=767 := by simp [mixFoldsQT,mixNeg,nR,cR]
  have f2 : mixFoldsQM false [(.inl (negRot L) : MixItem)]=768 := by simp [mixFoldsQM,mixNeg,nR,cR]
  have q := accFoldQ_counts L hw (accCItem L) st.2.2.1 st.2.2.2.2
  have qf := accFoldQF_counts L g (accCItem L)
  have pr := (accQ_item_prices L hw).2.2
  rw [accCMix_eq] at pr
  simp [mixFoldsQT,mixFoldsQM,mixNeg,nR,cR,nC] at pr
  have rel : accPriceQ (accCItem L)+256=accPrice (accCItem L) := by simp only [accPriceQ,accPrice]; omega
  rw [bodyC]
  simp only [toffoliCount_append,measurementCount_append]
  rw [f.1,f.2,qf.1,qf.2,q.1,q.2,f1,f2]
  constructor <;> omega

theorem bodyC_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (g : Wire) :
    ECDSAAdd.wires (bodyC L g)⊆(g::L.wires).toFinset := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_support L hw hn g false _ st.1
  have b := accFoldQF_support L hw hn g (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyC,wires_append,Finset.union_subset_iff]
  exact ⟨a,b⟩

theorem bodyC_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires) : GatePhysical (bodyC L g) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_physical L hw hn false _ st.1
  have b := accFoldQF_physical L hw hn g hg (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyC,gatePhysical_append]
  exact ⟨a,b⟩

theorem bodyC_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Challenge.gateSlots (bodyC L g)≤2*(41000+2*(20*(14*163))+(67*256+41)) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_gateSlots L hw false _ st.1 20 (by intro i hi a e; simp at hi; subst hi; cases e)
  have b := accFoldQF_gateSlots L hw g (accCItem L) st.2.2.1 st.2.2.2.2
  have lt : (accCItem L).terms.length=5 := by simp [accCItem,earlyHTerms]
  have lp : (accCItem L).pre.length=0 := rfl
  rw [lt,lp] at b
  simp only [List.length_singleton] at a
  simp only [bodyC,Challenge.gateSlots_append]
  omega

/-- C contribution with the complemented accumulator: plain orientation, plus `g·(2^163-1)`. -/
def resCF (g : Bool) (P O : Nat) : Nat :=
  ofCast false (measuredOrientationCast false O+(-(P : ZMod SquareReduction.p)*2^128)+
    ((if g then cFlipK else 0 : Nat) : ZMod SquareReduction.p))

theorem accC_zero (L : CuccaroStreamedSquareWideLayout) (t : BasisState) (hp : regValue L.core.product t=0) :
    Acc.accVal t 0 (accCItem L).spec=0 := by
  have z := (regValue_zero _ _).mp hp
  have h128 : regValue (L.core.product.drop 128) t=0 :=
    (regValue_zero _ _).mpr (fun q hq => z q (List.mem_of_mem_drop hq))
  have h256 : regValue (L.core.product.drop 256) t=0 :=
    (regValue_zero _ _).mpr (fun q hq => z q (List.mem_of_mem_drop hq))
  simp [accCItem,Acc.accVal,Acc.step,earlyHTerms,Acc.earlyTerm,posTop,h128,h256]

theorem accMiddleCF_body (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (M O : Nat) (hO : O<SquareReduction.p)
    (t : State) (m : List Bool) (pv : regValue L.core.product t.basis=M^2)
    (hM : t.basis control=false → M=0)
    (clean : L.PairClean t.basis) (outO : regValue L.core.out t.basis=O) :
    (run (bodyC L control) m t).phase=t.phase ∧
    regValue L.core.out (run (bodyC L control) m t).basis=resCF (t.basis control) (M^2) O ∧
    ∀q,q∉L.core.out → (run (bodyC L control) m t).basis q=t.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have gW : control∉L.wires := (List.nodup_cons.mp hn).1
  have views := accC_views L hw t.basis M pv
  rw [accCMix_eq] at views
  have v1 : ∀i∈[(.inl (negRot L) : MixItem)],MixView L t.basis i := fun i hi => views i (by simp at hi ⊢; exact Or.inl hi)
  have va : AccView L t.basis (accCItem L) := views (.inr (accCItem L)) (by simp)
  let mm := measurementCount (mixFoldsQ L false [.inl (negRot L)])
  let r1 := run (mixFoldsQ L false [.inl (negRot L)]) (m.take mm) t
  have e1 := mixFoldsQ_frame L hw nd t.basis clean false O hO [.inl (negRot L)] v1 t (m.take mm) ⟨outO,fun _ _ => rfl⟩
  let O1 := mixValue t.basis false O [.inl (negRot L)]
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have e2 := accFoldQF_frame L hw nd control gW t.basis (accCItem L) va clean O1 hO1 r1 (m.drop mm) e1.2
  rw [bodyC,run_append]
  refine ⟨e2.1.trans e1.1,?_,fun q hq => e2.2.2 q hq⟩
  rw [e2.2.1]
  have nR : (negRot L).negative=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have cast1 := mixValue_cast t.basis false O [.inl (negRot L)] hO
  have sum := (accC_mixSum L hw t.basis).trans (L.measuredC_sum hw t.basis (M^2) pv)
  rw [accCMix_eq] at sum
  simp only [mixFinal,mixNeg,nR,nC,mixSignedSum,mixSignedPayload,mixPayload,↓reduceIte,add_zero] at cast1 sum
  simp only [measuredOrientationCast,↓reduceIte,Bool.false_eq_true] at cast1
  have hA : Acc.accVal t.basis 0 (accCItem L).spec<2^163 := Acc.accVal_lt _ 163 _ 0 (by norm_num) va.specValid
  set A := Acc.accVal t.basis 0 (accCItem L).spec with hAdef
  set O1 := mixValue t.basis false O [.inl (negRot L)] with hO1def
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have hp1 : ((SquareReduction.p : Nat) : ZMod SquareReduction.p)=0 := ZMod.natCast_self _
  have e3 : ((SquareReduction.p-1-O1 : Nat) : ZMod SquareReduction.p)=-1-(O1 : ZMod SquareReduction.p) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one,hp1]; ring
  have target : ((((if t.basis control then cFlipK-A else A)+(SquareReduction.p-1-O1)) : Nat) : ZMod SquareReduction.p)=
      measuredOrientationCast false O+(-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)+
        ((if t.basis control then cFlipK else 0 : Nat) : ZMod SquareReduction.p) := by
    simp only [measuredOrientationCast,Bool.false_eq_true,↓reduceIte]
    cases hg : t.basis control
    · have m0 := hM hg
      have a0 : A=0 := by
        have pz : regValue L.core.product t.basis=0 := by rw [pv,m0]; rfl
        exact accC_zero L t.basis pz
      simp only [Bool.false_eq_true,↓reduceIte]
      rw [Nat.cast_add,e3,a0,Nat.cast_zero]
      rw [a0,Nat.cast_zero] at sum
      linear_combination cast1+sum
    · have hAK : A≤cFlipK := by unfold cFlipK; omega
      simp only [↓reduceIte]
      rw [Nat.cast_add,Nat.cast_sub hAK,e3]
      linear_combination cast1+sum
  unfold resCF ofCast
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [←target,ZMod.val_natCast]

def accBranchAK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.low (L.core.product.take 256) (mixFoldsQ L true (accAMixQ L))
def accBranchBK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.high (L.core.product.take 256) (mixFoldsQ L false (accBMixQ L))
def accMiddleCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.sum L.core.product (bodyC L control)
def accBranchCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  gPrep L++accMiddleCK L ext control++gClear L
def accPrefixK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  accBranchCK L ext control++accBranchBK L ext control++accBranchAK L ext control

theorem accBranchAK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchAK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchAK L ext control) records s).basis=
      resAQ ((if s.basis control then A else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchAK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := withMixedK_contribution L hw ext control hn L.core.low (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) true (accAMixQ L) s records hc dstZero
    O (M^2) (resAQ (M^2) O) hO ho (by rw [ha])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp i hi => accA_views L hw t M mb hp i (accAMixQ_mem L i hi))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accAMixQ_sum L t).trans ((accA_mixSum L hw t).trans (L.measuredA_sum hw t (M^2) hp pb)))
    (ofCast_lt _ _) (by
      rw [(accQ_orientations L).1]
      exact cast_ofCast _ _) he hz (accQ_static L hw).1
  exact result

theorem accBranchBK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchBK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchBK L ext control) records s).basis=
      resBQ ((if s.basis control then B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchBK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := withMixedK_contribution L hw ext control hn L.core.high (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) false (accBMixQ L) s records hc dstZero
    O (M^2) (resBQ (M^2) O) hO ho (by rw [hb])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp i hi => accB_views L hw t M mb hp i (accBMixQ_mem L i hi))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accBMixQ_sum L t).trans ((accB_mixSum L hw t (M^2) hp pb).trans (L.measuredB_sum hw t (M^2) hp pb)))
    (ofCast_lt _ _) (by
      rw [(accQ_orientations L).2.1]
      exact cast_ofCast _ _) he hz (accQ_static L hw).2
  exact result

theorem accMiddleCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accMiddleCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accMiddleCK L ext control) records s).basis=
      resCF (s.basis control) ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accMiddleCK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (bodyC L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (bodyC_support L hw nd control hw'))
  apply withLowK2_correct L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len (bodyC L control) hbody
    s records hc hp0 hz
  intro t m dstValue same
  have ctrlT : t.basis control=s.basis control :=
    same control (fun h => (List.nodup_cons.mp hn).1
      (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]))
  have pv : regValue L.core.product t.basis=M^2 := by simpa [M,hs] using dstValue
  have clean := L.measured_product_frame_clean nd L.core.product (fun _ => le_rfl) s.basis t.basis hc same
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q
      (fun hp => List.disjoint_left.mp (L.product_out_disjoint nd) hp hq))).trans ho
  have r := accMiddleCF_body L hw control hn M O hO t m pv
    (by intro h; rw [ctrlT] at h; simp [M,h]) clean outO
  rw [ctrlT] at r
  exact r

theorem accBranchCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchCK L ext control) records s).basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchCK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := accMiddleCK L ext control
  let mp := measurementCount (gPrep L)
  let rest := records.drop mp
  let u := run (gPrep L) (records.take mp) s
  let v := run middle (rest.take (measurementCount middle)) u
  let out := run (gClear L) (rest.drop (measurementCount middle)) v
  have prep := gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have hzU : regValue ext u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (sum_in L control q bad)))).trans hz
  have used := accMiddleCK_correct L hw ext control hn (A+B) O hO u
    (rest.take (measurementCount middle)) prep.2.1 outU productU cleanU he hzU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have workRestore : regValue L.core.work restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hc.work
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [hq])).2
    simp [restoreBase,away]
  have cleared := gClear_frame L hw nd restoreBase A B lowRestore bound padRestore cinRestore workRestore
    v (rest.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  simpa [accBranchCK,middle,u,v,out,rest,mp,run_append] using final

theorem cbaF_complete_exact (enabled : Bool) (A B O : Nat) :
    resAQ ((if enabled then A else 0)^2)
      (resBQ ((if enabled then B else 0)^2) (resCF enabled ((if enabled then A+B else 0)^2) O))=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resCF enabled PC O
  let OB := resBQ PB OC
  let OA := resAQ PA OB
  have ec : measuredOrientationCast false OC=measuredOrientationCast false O+(-(PC : ZMod SquareReduction.p)*2^128)+
      ((if enabled then cFlipK else 0 : Nat) : ZMod SquareReduction.p) := cast_ofCast _ _
  have eb : measuredOrientationCast true OB=measuredOrientationCast false OC+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB) := cast_ofCast _ _
  have ea : measuredOrientationCast false OA=measuredOrientationCast true OB+((PA : ZMod SquareReduction.p)*2^128-PA) :=
    cast_ofCast _ _
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have oaBound : OA<SquareReduction.p := ofCast_lt _ _
  have targetBound : (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p<
      SquareReduction.p := Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have cast : (OA : ZMod SquareReduction.p)=
      (((subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p : Nat) :
        ZMod SquareReduction.p) := by
    rw [ZMod.natCast_mod,Nat.cast_add,subModValue_cast]
    linear_combination ea+eb+ec+identity
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt oaBound,ZMod.val_natCast_of_lt targetBound] using value

theorem accPrefixK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accPrefixK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accPrefixK L ext control) records s).basis=
      ((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then cFlipK else 0))%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (accPrefixK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resCF enabled PC O
  let OB := resBQ PB OC
  let OA := resAQ PA OB
  let restC := records.drop (measurementCount (accBranchCK L ext control))
  let restB := restC.drop (measurementCount (accBranchBK L ext control))
  let u := run (accBranchCK L ext control) (records.take (measurementCount (accBranchCK L ext control))) s
  let v := run (accBranchBK L ext control) (restC.take (measurementCount (accBranchBK L ext control))) u
  let w := run (accBranchAK L ext control) restB v
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have ec := accBranchCK_correct L hw ext control hn A B O hO s
    (records.take (measurementCount (accBranchCK L ext control))) rfl sumB sumBound ho hp0 hc he hz
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OC ⟨ec.2.1,ec.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ec.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B := regValue_congr _ _ _ (fun q hq => ec.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ec.2.2 control ctrlAway
  have eb := accBranchBK_correct L hw ext control hn B OC (ofCast_lt _ _) u
    (restC.take (measurementCount (accBranchBK L ext control))) highU ec.2.1 productU cleanU he
    ((regValue_congr _ _ _ (fun q hq => ec.2.2 q (ext_out L control ext he q hq))).trans hz)
  rw [ctrlU] at eb
  have sameV (q : Wire) (hq : q∉L.core.out) : v.basis q=s.basis q :=
    (eb.2.2 q hq).trans (ec.2.2 q hq)
  have cleanV : L.PairClean v.basis :=
    L.squareFrame_clean nd s.basis v.basis OB ⟨eb.2.1,sameV⟩ hc
  have productV : regValue L.core.product v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sameV q (List.disjoint_left.mp disProduct hq))).trans hp0
  have lowV : regValue L.core.low v.basis=A :=
    regValue_congr _ _ _ (fun q hq => sameV q (lowAway q hq))
  have ctrlV : v.basis control=enabled := sameV control ctrlAway
  have ea := accBranchAK_correct L hw ext control hn A OB (ofCast_lt _ _) v restB lowV eb.2.1 productV cleanV he
    ((regValue_congr _ _ _ (fun q hq => sameV q (ext_out L control ext he q hq))).trans hz)
  rw [ctrlV] at ea
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ea.2.2 q hq).trans (sameV q hq)
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have fullValue : regValue L.core.out w.basis=
      ((O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if enabled then cFlipK else 0))%SquareReduction.p := by
    have exactResult := cbaF_complete_exact enabled A B O
    rw [split] at exactResult
    unfold subModValue at exactResult
    rw [ea.2.1]
    exact exactResult
  have final : w.phase=s.phase ∧ regValue L.core.out w.basis=
      ((O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if enabled then cFlipK else 0))%SquareReduction.p ∧
      ∀q,q∉L.core.out → w.basis q=s.basis q :=
    ⟨ea.1.trans (eb.1.trans ec.1),fullValue,sameW⟩
  simpa [accPrefixK,u,v,w,restB,restC,enabled,run_append,Nat.add_assoc] using final


theorem accPrefixK_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (he : 300≤ext.length) :
    toffoliCount (accPrefixK L ext control)=4*lowkcost2 128+2*lowkcost2 129+13554 ∧ measurementCount (accPrefixK L ext control)=4*lowkcost2 128+2*lowkcost2 129+13566 := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := withLowK2_counts L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) (by omega) (by omega) (by omega) he
  have b := withLowK2_counts L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) (by omega) (by omega) (by omega) he
  have c := withLowK2_counts L hw ext control L.core.sum L.core.product
    (bodyC L control) (by omega) (by omega) (by rw [hw.core.product,su]) he
  have fa := mixFoldsQ_counts L hw true (accAMixQ L) stQ.1
  have fb := mixFoldsQ_counts L hw false (accBMixQ L) stQ.2
  have fc := bodyC_counts L hw control
  have prices := accQ_item_prices L hw
  rw [prices.1.1,prices.1.2] at fa
  rw [prices.2.1.1,prices.2.1.2] at fb
  have sum := gSum_counts L hw
  rw [lo] at a
  rw [hi] at b
  rw [su] at c
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    sum.1.1,sum.1.2,sum.2.1,sum.2.2]
  constructor <;> omega

theorem accPrefixK_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    ECDSAAdd.wires (accPrefixK L ext control)⊆(control::L.wires++ext).toFinset := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have a := mixFoldsQ_support L hw hn control true (accAMixQ L) stQ.1
  have b := mixFoldsQ_support L hw hn control false (accBMixQ L) stQ.2
  have c := bodyC_support L hw hn control
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have sa := withLowK2_support L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) hl hp (by omega) (by omega) (by omega) he a
  have sb := withLowK2_support L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) hb hp (by omega) (by omega) (by omega) he b
  have sc := withLowK2_support L hw ext control L.core.sum L.core.product
    (bodyC L control) hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) he c
  have embed : (control::L.wires).toFinset⊆(control::L.wires++ext).toFinset := by
    intro q hq; simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto
  have prep := (gSum_support L hw control).1.trans embed
  have unprep := (gSum_support L hw control).2.trans embed
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,wires_append,
    Finset.union_subset_iff]
  exact ⟨⟨⟨⟨prep,sc⟩,unprep⟩,sb⟩,sa⟩

theorem accPrefixK_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control :: L.wires).Nodup) (he : ExtOK L control ext) :
    GatePhysical (accPrefixK L ext control) := by
  have nd := (List.nodup_cons.mp hn).2
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := withLowK2_physical L hw control hn _ _ hl hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (mixFoldsQ_physical L hw nd true (accAMixQ L) stQ.1)
  have b := withLowK2_physical L hw control hn _ _ hb hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (mixFoldsQ_physical L hw nd false (accBMixQ L) stQ.2)
  have c := withLowK2_physical L hw control hn _ _ hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) ext he.nodup he.away he.len _
    (bodyC_physical L hw nd control (List.nodup_cons.mp hn).1)
  have prep := (gSum_physical L hw nd).1
  have clear := (gSum_physical L hw nd).2
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,gatePhysical_append]
  exact ⟨⟨⟨⟨prep,c⟩,clear⟩,b⟩,a⟩

theorem accPrefixK_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (accPrefixK L ext control) ≤ 8000000 := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have bd (items : List MixItem) (h : items=accAMixQ L ∨ items=accBMixQ L ∨ items=accCMix L) :
      ∀i∈items,∀a,i=.inr a → a.terms.length≤20 ∧ a.pre.length≤4 := by
    intro i hi a e
    subst e
    rcases h with rfl|rfl|rfl <;>
      simp [accAMixQ,accBMixQ,accCMix] at hi <;> rw [hi] <;>
      simp [sortedItems,accARaw,accBRaw,accCRaw,termsB,earlyHTerms,Acc.earlyTerm,preW,nafMinusOneItems,List.filter_cons,posTop]
  have ha := mixFoldsQ_gateSlots L hw true (accAMixQ L) stQ.1 20 (bd _ (Or.inl rfl))
  have hb := mixFoldsQ_gateSlots L hw false (accBMixQ L) stQ.2 20 (bd _ (Or.inr (Or.inl rfl)))
  have hc := bodyC_gateSlots L hw control
  have la : (accAMixQ L).length = 3 := rfl
  have lb : (accBMixQ L).length = 7 := rfl
  have lc : (accCMix L).length = 2 := rfl
  rw [la] at ha
  rw [lb] at hb
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := withLowK2_gateSlots_le L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) (by omega) (by omega) (by omega) he
  have b := withLowK2_gateSlots_le L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) (by omega) (by omega) (by omega) he
  have c := withLowK2_gateSlots_le L hw ext control L.core.sum L.core.product
    (bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have gs := gSum_gateSlots L hw
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.OwnAll12Square

end

section
-- ===== FastSquare =====

/-! Point-layout binding of the sign-grouped streamed square, with the same
pool relabeling as the Skywalk Step 4 square. -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.OwnAll12Square
open Arithmetic ControlledPointLayout Secp256k1 CompressedPointSquare

/-- Zero pool sites 978..1028, 1284..1529 and 1533..1535: in the
certified site inventory, outside the square's placed prefix, fixed by its pool permutations. -/
def kext (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 978 51++wireBlock L.core.poolWire 1284 246++wireBlock L.core.poolWire 1533 3

theorem kext_index (L : ControlledPointLayout) (q : Wire) (hq : q∈kext L) :
    ∃i,978 ≤ i ∧ i < 1536 ∧ (i < 1029 ∨ (1284 ≤ i ∧ i < 1530) ∨ 1533 ≤ i) ∧ q=L.core.poolWire i := by
  rcases List.mem_append.mp hq with h|h
  · rcases List.mem_append.mp h with h|h <;> obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h <;>
      simp only [List.mem_range'_1] at hj <;> exact ⟨j,by omega,by omega,by omega,rfl⟩
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    exact ⟨j,by omega,by omega,by omega,rfl⟩

theorem dialogPool_nodup' (L : ControlledPointLayout) (hn : L.wires.Nodup) : L.dialogPool.Nodup :=
  (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.1

theorem kpool_block (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogPool.take 2613=wireBlock L.core.poolWire 0 2613 := by
  simp only [dialogPool,List.take_take,Nat.min_self]
  exact (L.core.pool_prefix hw 2613 (by omega)).symm

theorem kpool_inj (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i j : Nat) (hi : i < 2613) (hj : j < 2613)
    (h : L.core.poolWire i = L.core.poolWire j) : i = j := by
  have nd : (wireBlock L.core.poolWire 0 2613).Nodup := by
    rw [← kpool_block L hw]
    exact (List.take_sublist _ _).nodup (dialogPool_nodup' L hn)
  exact List.inj_on_of_nodup_map nd (x := i) (y := j)
    (by simp [List.mem_range'_1]; omega) (by simp [List.mem_range'_1]; omega) h

theorem kext_mem (L : ControlledPointLayout) (hw : L.Widths) (q : Wire) (hq : q∈kext L) :
    q∈L.dialogPool := by
  obtain ⟨i,h1,h2,h3,rfl⟩ := kext_index L q hq
  have h : L.core.poolWire i∈L.dialogPool.take 2613 := by
    rw [kpool_block L hw]
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  exact List.mem_of_mem_take h

theorem kext_props (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (kext L).Nodup ∧ ∀q∈kext L,q∉L.dialogPool.take 945 := by
  refine ⟨?_,?_⟩
  · have e : kext L=(List.range' 978 51++List.range' 1284 246++List.range' 1533 3).map L.core.poolWire := by
      simp only [kext,wireBlock,List.map_append]
    rw [e]
    apply List.Nodup.map_on
    · intro x hx y hy hxy
      simp only [List.mem_append,List.mem_range'_1] at hx hy
      exact kpool_inj L hw hn x y (by omega) (by omega) hxy
    · apply List.nodup_append.mpr
      refine ⟨List.nodup_append.mpr ⟨List.nodup_range',List.nodup_range',?_⟩,List.nodup_range',?_⟩
      · intro x hx y hy hxy
        simp only [List.mem_range'_1] at hx hy
        omega
      · intro x hx y hy hxy
        simp only [List.mem_append,List.mem_range'_1] at hx hy
        omega
  · intro q hq hm
    obtain ⟨i,h1,h2,h3,rfl⟩ := kext_index L q hq
    have b : L.dialogPool.take 945=wireBlock L.core.poolWire 0 945 := by
      simp only [dialogPool,List.take_take,Nat.min_eq_left (show 945 ≤ 2613 by omega)]
      exact (L.core.pool_prefix hw 945 (by omega)).symm
    rw [b] at hm
    obtain ⟨j,hj,e⟩ := List.mem_map.mp hm
    simp only [List.mem_range'_1] at hj
    have := kpool_inj L hw hn j i (by omega) (by omega) e
    omega

theorem kext_not_resident (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈kext L) (hr : q∈PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags) :
    False :=
  (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.2 q (by simpa [dialogUsedWires] using hr) q
    (kext_mem L hw q hq) rfl

theorem kext_fixed (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈kext L) :
    poolPermutation L.core.poolWire (layout_bounded_injective L hw hn) q=q := by
  obtain ⟨j,hj1,hj2,hj3,rfl⟩ := kext_index L q hq
  apply outside_fixed
  · rintro ⟨i,h1,h2,e⟩
    have := kpool_inj L hw hn j i (by omega) (by omega) e
    omega
  · rintro ⟨i,h1,h2,e⟩
    have := kpool_inj L hw hn j i (by omega) (by omega) e
    omega

theorem kext_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ExtOK L.dialogStreamedSquareWide L.core.generic (kext L) := by
  have kp := kext_props L hw hn
  refine ⟨kp.1,?_,by simp [kext,wireBlock_length]⟩
  intro q hq hm
  rw [List.mem_cons,L.streamedSquare_wires_eq hw] at hm
  simp only [List.mem_append] at hm
  rcases hm with h|(h|h)|h
  · subst h
    exact kext_not_resident L hw hn _ hq (by simp [inPlaceFlags])
  · exact kext_not_resident L hw hn q hq (by simp [PointAddLayout.pointWires,h])
  · exact kext_not_resident L hw hn q hq (by simp [PointAddLayout.pointWires,h])
  · apply kp.2 q hq
    have e : (L.dialogPool.take 945).take 775=L.dialogPool.take 775 := by
      rw [List.take_take,Nat.min_eq_left (by omega)]
    rw [←e] at h
    exact List.mem_of_mem_take h

def fastCandidate (L : ControlledPointLayout) : Program :=
  accPrefixK L.dialogStreamedSquareWide (kext L) L.core.generic

theorem fastCandidate_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastCandidate L)=4*lowkcost2 128+2*lowkcost2 129+13554 ∧ measurementCount (fastCandidate L)=4*lowkcost2 128+2*lowkcost2 129+13566 :=
  accPrefixK_counts L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
    L.core.generic (by simp [kext,wireBlock_length])

theorem fastCandidate_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (fastCandidate L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776++kext L).toFinset := by
  have support := accPrefixK_support L.dialogStreamedSquareWide
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn) (kext L)
    L.core.generic (by simp [kext,wireBlock_length])
  have embed : (L.core.generic::L.dialogStreamedSquareWide.wires++kext L).toFinset⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776++kext L).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    have small : L.dialogPool.take 775⊆L.dialogPool.take 776 := by
      intro q hq
      have e : (L.dialogPool.take 776).take 775=L.dialogPool.take 775 := by
        rw [List.take_take,Nat.min_eq_left (by omega)]
      rw [←e] at hq
      exact List.mem_of_mem_take hq
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp : q∈L.dialogPool.take 775 → q∈L.dialogPool.take 776 := fun h => small h
    tauto
  exact support.trans embed

theorem fastCandidate_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCandidate L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCandidate L) m s).basis=
      ((X+p-(if B then Y*Y else 0)%p)%p+(if B then cFlipK else 0))%p ∧
    ∀q,q∉L.point.x → (run (fastCandidate L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := accPrefixK_correct K hwK (kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean (kext_ok L hw hn) hz
  simpa only [fastCandidate,hb,hp,pow_two] using kernel

theorem fastCandidate_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (fastCandidate L) := by
  apply accPrefixK_physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
  · have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢; omega
  · exact kext_ok L hw hn

/-- Computable relabeled square: the emitted Step 4 program. -/
def fastSquare (L : ControlledPointLayout) : Program :=
  renameProgram (labelFn L.core.poolWire) (fastCandidate L)

noncomputable def fastSquareN (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : Program :=
  renameProgram (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) (fastCandidate L)

theorem fastSquare_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    fastSquare L=fastSquareN L hw hn := by
  apply renameProgram_congr_support
  intro q _
  exact label_matches _ (layout_bounded_injective L hw hn) q

private theorem pool_away_x' (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have nd := L.dialogUsed_nodup hn
  have dis := (List.nodup_append'.mp nd).2.2
  intro hx
  have res : q∈residents L := by
    simp only [residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis res hq

private theorem pull_injective' (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t eq
  apply State.extensionality
  · have ph := congrArg (fun u : State => u.phase) eq
    exact ph
  · funext q
    have bit := congrArg (fun u : State => u.basis (e.symm q)) eq
    simpa only [pullState,e.apply_symm_apply] using bit

section StateEq
attribute [local irreducible] run wires fastCandidate

theorem fastSquare_state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    run (fastSquare L) m s=run (fastCandidate L) m s := by
  let e := poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)
  have old := fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (fastCandidate L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (pool_away_x' L hn q hq)).trans (cleanIn q hq)
  have input := zero_pool_boundary L hw hn s cleanIn
  have output := zero_pool_boundary L hw hn (run (fastCandidate L) m s) cleanOut
  rw [fastSquare_eq L hw hn,fastSquareN]
  apply pull_injective' e
  have semantic := run_rename e e.injective (fastCandidate L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

theorem fastSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (fastSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastSquare L) m s).basis=
      ((X+p-(if B then Y*Y else 0)%p)%p+(if B then cFlipK else 0))%p ∧
    ∀q,q∉L.point.x → (run (fastSquare L) m s).basis q=s.basis q := by
  rw [fastSquare_state_eq L hw hn X Y B hX s m hb hx hy hc]
  exact fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc

end StateEq

theorem fastSquare_physical (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (fastSquare L) := by
  rw [fastSquare_eq L hw hn]
  apply gatePhysical_rename _ (poolPermutation L.core.poolWire
    (layout_bounded_injective L hw hn)).injective
  exact fastCandidate_physical L hw hn

theorem fastSquare_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (fastSquare L) ≤ 8000000 := by
  simpa only [fastSquare,Baselines.rename_gateSlots,fastCandidate]
    using accPrefixK_gateSlots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
      L.core.generic (by simp [kext,wireBlock_length])

end ECDSAAdd.Entrant.OwnAll12Square

end


-- ALL12 COMPONENT SquareTriple

namespace ECDSAAdd.Entrant.OwnAll12Square
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
private theorem sub_val' (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

section SquareStep
attribute [local irreducible] run fastSquare fastCandidate
private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

theorem fast_step_square (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (fastSquare L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (cFlipK : Fp) else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastSquare_correct L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  have hK : ((cFlipK : Nat) : Fp).val=cFlipK := ZMod.val_natCast_of_lt (by norm_num [cFlipK,p])
  rw [ZMod.val_add,sub_val']
  cases G
  · simpa using hx
  · simpa [ZMod.val_mul,hK] using hx

end SquareStep
end ECDSAAdd.Entrant.OwnAll12Square


-- ALL12 COMPONENT Placement

namespace ECDSAAdd.Entrant.OwnAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

def SquareCorrect (L : ControlledPointLayout) (P : Program) : Prop :=
  ∀ (X Y : Fp) (G : Bool) (origin : BasisState),
    Triple (PointDialogValues L X Y G origin) P
      (PointDialogValues L (X-(if G then Y*Y else 0)+
        (if G then (OwnAll12Square.cFlipK : Fp) else 0)) Y G origin)

theorem relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool)
    (hf : ∀q,q∉L.dialogPool → e q=q) (P : Program) (correct : SquareCorrect L P) :
    SquareCorrect L (renameProgram e P) := by
  intro X Y G origin s m v
  have old:=correct X Y G origin s m v
  have eq:=Square5Placement.pool_relabel_state_eq L e hp hf P s m v.clean old.2.clean
  simpa only [eq] using old

def initial (L : ControlledPointLayout) : Program :=
  renameProgram (Square5Placement.blockPerm L 202) (OwnAll12Square.fastCandidate L)
def plus (L : ControlledPointLayout) : Program := renameProgram (OwnPlusSquare.swap L) (initial L)
def guard (L : ControlledPointLayout) : Program := renameProgram (OwnGuardSquare.swap L) (plus L)
def minus (L : ControlledPointLayout) : Program := renameProgram (OwnQ4Square.swap L) (guard L)
def program (L : ControlledPointLayout) : Program := renameProgram (OwnQ5Square.swap L) (minus L)

theorem candidate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrect L (OwnAll12Square.fastCandidate L) := by
  intro X Y G origin s m v
  have old:=OwnAll12Square.fast_step_square L hw hn X Y G origin s m v
  rw [OwnAll12Square.fastSquare_state_eq L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean] at old
  exact old

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrect L (program L) := by
  have a:=relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) _ (candidate_correct L hw hn)
  have b:=relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw)
    (OwnPlusSquare.outside L hw) _ a
  have c:=relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw)
    (OwnGuardSquare.outside L hw) _ b
  have d:=relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw)
    (OwnQ4Square.outside L hw) _ c
  exact relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw)
    (OwnQ5Square.outside L hw) _ d

end ECDSAAdd.Entrant.OwnAll12Placed


-- ALL12 COMPONENT Resources

namespace ECDSAAdd.Entrant.OwnAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=4*lowkcost2 128+2*lowkcost2 129+13554 ∧
    measurementCount (program L)=4*lowkcost2 128+2*lowkcost2 129+13566 := by
  have a:=renameProgram_counts (Square5Placement.blockPerm L 202) (OwnAll12Square.fastCandidate L)
  have b:=renameProgram_counts (OwnPlusSquare.swap L) (initial L)
  have c:=renameProgram_counts (OwnGuardSquare.swap L) (plus L)
  have d:=renameProgram_counts (OwnQ4Square.swap L) (guard L)
  have e:=renameProgram_counts (OwnQ5Square.swap L) (minus L)
  have base:=OwnAll12Square.fastCandidate_counts L hw
  exact ⟨e.1.trans (d.1.trans (c.1.trans (b.1.trans (a.1.trans base.1)))),
    e.2.trans (d.2.trans (c.2.trans (b.2.trans (a.2.trans base.2))))⟩

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  apply gatePhysical_rename (OwnQ5Square.swap L) (OwnQ5Square.swap L).injective
  apply gatePhysical_rename (OwnQ4Square.swap L) (OwnQ4Square.swap L).injective
  apply gatePhysical_rename (OwnGuardSquare.swap L) (OwnGuardSquare.swap L).injective
  apply gatePhysical_rename (OwnPlusSquare.swap L) (OwnPlusSquare.swap L).injective
  exact gatePhysical_rename (Square5Placement.blockPerm L 202)
    (Square5Placement.blockPerm L 202).injective _ (OwnAll12Square.fastCandidate_physical L hw hn)

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 := by
  simpa only [program,minus,guard,plus,initial,Baselines.rename_gateSlots,
    OwnAll12Square.fastCandidate] using
      OwnAll12Square.accPrefixK_gateSlots_le L.dialogStreamedSquareWide
        (L.dialogStreamedSquareWide_widths hw) (OwnAll12Square.kext L)
        L.core.generic (by simp [OwnAll12Square.kext,wireBlock_length])

end ECDSAAdd.Entrant.OwnAll12Placed


-- ALL12 COMPONENT Support
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem swap_support (P : Program) (a b : Wire) (S : Finset Wire)
    (old : wires P⊆S) (ha : a∈S) (hb : b∈S) :
    wires (renameProgram (Equiv.swap a b) P)⊆S := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp hq
  by_cases x:w=a
  · subst w; simpa only [Equiv.swap_apply_left] using hb
  · by_cases y:w=b
    · subst w; simpa only [Equiv.swap_apply_right] using ha
    · simpa only [Equiv.swap_apply_of_ne_of_ne x y] using old used

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L) ⊆ (OB5Support.sites L).toFinset := by
  have oldGuard : wires (guard L)⊆(OB5Support.sites L).toFinset := by
    have previous : wires (plus L)⊆(OB5Support.sites L).toFinset := by
      have old : wires (initial L)⊆(OB5Support.sites L).toFinset := by
        rw [initial,renameProgram_support]
        intro q hq
        obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
        have support := OwnAll12Square.fastCandidate_support L hw hn used
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at support
        apply List.mem_toFinset.mpr
        rcases support with h | h | h | h | h
        · subst old
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _
            (resident_away L hn _ (by simp [CompressedPointSquare.residents, inPlaceFlags]))]
          simp [OB5Support.sites]
        · have away := resident_away L hn old (by simp [CompressedPointSquare.residents, PointAddLayout.pointWires, h])
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away]
          simp only [OB5Support.sites, List.mem_cons, List.mem_append]
          exact Or.inl (Or.inr h)
        · have away := resident_away L hn old (by simp [CompressedPointSquare.residents, PointAddLayout.pointWires, h])
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away]
          simp only [OB5Support.sites, List.mem_cons, List.mem_append]
          exact Or.inl (Or.inl (Or.inr h))
        · rw [pool_block L hw 776 (by omega)] at h
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
          have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
          rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)]
          apply OB5Support.pool_in_sites
          apply OB5Support.pool_mem
          unfold Square5Placement.blockIndex
          split_ifs <;> omega
        · obtain ⟨i, h1, h2, h3, rfl⟩ := OwnAll12Square.kext_index L _ h
          rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)]
          apply OB5Support.pool_in_sites
          apply OB5Support.pool_mem
          unfold Square5Placement.blockIndex
          split_ifs <;> omega
      exact swap_support (initial L) (L.core.poolWire 766) (L.core.poolWire 1530) _ old
        (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 766 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
        (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1530 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
    exact swap_support (plus L) (L.core.poolWire 765) (L.core.poolWire 1531) _ previous
      (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 765 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
      (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1531 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
  have oldQ4 := swap_support (guard L) (L.core.poolWire 767) (L.core.poolWire 1532) _ oldGuard
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 767 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1532 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

  exact swap_support (minus L) (L.core.poolWire 770) (L.core.poolWire 1536) _ oldQ4
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 770 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1536 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

end ECDSAAdd.Entrant.OwnAll12Placed


-- ALL12 COMPONENT Omissions
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem q5_Square770_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem original_spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (n : Nat) (allowed : n∈[1530,1531,1532,1536,1537]) :
    L.core.poolWire n∉wires (initial L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
  rw [initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=OwnAll12Square.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=q5_Square770_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · have away:=q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · have away:=q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

theorem swap_target_free (P : Program) (a b : Wire) (free : b∉wires P) :
    a∉wires (renameProgram (Equiv.swap a b) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have back : (Equiv.swap a b) b=a := Equiv.swap_apply_right _ _
  have same : old=b := (Equiv.swap a b).injective (e.trans back.symm)
  exact free (same ▸ used)

private theorem fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b n : Nat) (ha : a<2613) (hb : b<2613) (hnn : n<2613)
    (hna : n≠a) (hnb : n≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)


theorem free766 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 766∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1530 (by simp)
  have p1 : L.core.poolWire 766∉wires (plus L) :=
    swap_target_free (initial L) (L.core.poolWire 766) (L.core.poolWire 1530) p0
  have p2 : L.core.poolWire 766∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 765 1531 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 766∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 767 1532 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 766∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 770 1536 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free765 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 765∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1531 (by simp)
  have p1 : L.core.poolWire 1531∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 766 1530 1531 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 765∉wires (guard L) :=
    swap_target_free (plus L) (L.core.poolWire 765) (L.core.poolWire 1531) p1
  have p3 : L.core.poolWire 765∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 767 1532 765 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 765∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 770 1536 765 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free767 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 767∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1532 (by simp)
  have p1 : L.core.poolWire 1532∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 766 1530 1532 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1532∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 765 1531 1532 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 767∉wires (minus L) :=
    swap_target_free (guard L) (L.core.poolWire 767) (L.core.poolWire 1532) p2
  have p4 : L.core.poolWire 767∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 770 1536 767 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free770 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 770∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1536 (by simp)
  have p1 : L.core.poolWire 1536∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 766 1530 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1536∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 765 1531 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1536∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 767 1532 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 770∉wires (program L) :=
    swap_target_free (minus L) (L.core.poolWire 770) (L.core.poolWire 1536) p3
  exact p4

theorem free1537 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1537∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1537 (by simp)
  have p1 : L.core.poolWire 1537∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 766 1530 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1537∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 765 1531 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1537∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 767 1532 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1537∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 770 1536 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

end ECDSAAdd.Entrant.OwnAll12Placed


-- ALL12 COMPONENT PlacementQ6
namespace ECDSAAdd.Entrant.OwnAll12PlacedQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

def swap (L : ControlledPointLayout) : Equiv.Perm Wire :=
  Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)
def program (L : ControlledPointLayout) : Program :=
  renameProgram (swap L) (OwnAll12Placed.program L)

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


theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    OwnAll12Placed.SquareCorrect L (program L) :=
  OwnAll12Placed.relabel L (swap L) (pool L hw) (outside L hw) _
    (OwnAll12Placed.correct L hw hn)

theorem retired_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1285∉wires (program L) :=
  OwnAll12Placed.swap_target_free _ _ _ (OwnAll12Placed.free1537 L hw hn)

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=4*lowkcost2 128+2*lowkcost2 129+13554 ∧
    measurementCount (program L)=4*lowkcost2 128+2*lowkcost2 129+13566 := by
  have e:=renameProgram_counts (swap L) (OwnAll12Placed.program L)
  have c:=OwnAll12Placed.counts L hw
  exact ⟨e.1.trans c.1,e.2.trans c.2⟩

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) :=
  gatePhysical_rename (swap L) (swap L).injective _ (OwnAll12Placed.physical L hw hn)

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 :=
  (Baselines.rename_gateSlots _ _).le.trans (OwnAll12Placed.slots L hw)

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  OwnAll12Placed.swap_support _ _ _ _ (OwnAll12Placed.support L hw hn)
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1285
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1537
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

private theorem fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (n : Nat) (hnn : n<2613) (a : n≠1285) (b : n≠1537) : swap L (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact a (pool_inj L hw hn n 1285 hnn (by omega) eq)
  · intro eq;exact b (pool_inj L hw hn n 1537 hnn (by omega) eq)

theorem free765 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 765∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 765 (by omega) (by omega) (by omega))
    (OwnAll12Placed.free765 L hw hn)

theorem free766 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 766∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 766 (by omega) (by omega) (by omega))
    (OwnAll12Placed.free766 L hw hn)

theorem free767 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 767∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 767 (by omega) (by omega) (by omega))
    (OwnAll12Placed.free767 L hw hn)

theorem free770 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 770∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (fix L hw hn 770 (by omega) (by omega) (by omega))
    (OwnAll12Placed.free770 L hw hn)

end ECDSAAdd.Entrant.OwnAll12PlacedQ6


-- ALL12 COMPONENT TailOmissions
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem q5_Square770_tail_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem initial1800_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (initial L) := by
  rw [initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=OwnAll12Square.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=q5_Square770_tail_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · have away:=q5_Square770_tail_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · have away:=q5_Square770_tail_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1800 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1800 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

private theorem fix1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b : Nat) (ha : a<2613) (hb : b<2613) (hna : 1800≠a) (hnb : 1800≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire 1800)=L.core.poolWire 1800 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn 1800 a (by omega) ha eq)
  · intro eq;exact hnb (pool_inj L hw hn 1800 b (by omega) hb eq)

theorem free1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (program L) := by
  have p0:=initial1800_free L hw hn
  have p1 : L.core.poolWire 1800∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix1800 L hw hn 766 1530 (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1800∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix1800 L hw hn 765 1531 (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1800∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix1800 L hw hn 767 1532 (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1800∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (fix1800 L hw hn 770 1536 (by omega) (by omega) (by omega) (by omega)) p3
  exact p4
end ECDSAAdd.Entrant.OwnAll12Placed
namespace ECDSAAdd.Entrant.OwnAll12PlacedQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

theorem free1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (program L) := by
  have same: swap L (L.core.poolWire 1800)=L.core.poolWire 1800 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro e
      have :=pool_inj L hw hn 1800 1285 (by omega) (by omega) e
      omega
    · intro e
      have :=pool_inj L hw hn 1800 1537 (by omega) (by omega) e
      omega
  exact OwnPlusHost.rename_avoid _ _ _ same (OwnAll12Placed.free1800 L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) :
    L.core.poolWire k∉wires (program L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact free1800 L hw hn
  · exact free766 L hw hn
  · exact free765 L hw hn
  · exact free767 L hw hn
  · exact free770 L hw hn
  · exact retired_free L hw hn
end ECDSAAdd.Entrant.OwnAll12PlacedQ6


-- ALL12 COMPONENT All12Generic
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.All12Generic
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
  EntryFuseFinite ExitFusionResearch

/-- Source-only generic tail parameter; the actual shortened multiplier is supplied separately. -/
def generic (L : ControlledPointLayout) (D : Fp→Program) (S P : Program) (cx cy : Fp) : Program :=
  fastConstAdd L L.point.x (-cx) ++ D (-cy) ++
  S ++ fastConstAdd L L.point.x (3*cx-(2^163-1 : Nat)) ++
  P ++ exitY L cy ++ fastConstNeg L cx

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
variable (D : Fp→Program) (S P : Program) (halfCorrect : HalfMultiplyCorrect L P)
variable (divisionCorrect : ∀(X Y k : Fp)(G : Bool)(origin : BasisState),X≠0 →
  Triple (PointDialogValues L X Y G origin) (D k)
    (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin))
variable (squareCorrect : ∀(X Y : Fp)(G : Bool)(origin : BasisState),
  Triple (PointDialogValues L X Y G origin) S
    (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (2^163-1 : Nat) else 0)) Y G origin))
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
  have h4 := fastStep_addX L hw hn ((X-cx)-a*a+(2^163-1 : Nat)) a true origin (3*cx-(2^163-1 : Nat))
  simp only [if_true] at h4
  have hd4 : ((X-cx)-a*a+(2^163-1 : Nat))+(3*cx-(2^163-1 : Nat))=d := by
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
  have h4 := fastStep_addX L hw hn X (Y/X) false origin (3*cx-(2^163-1 : Nat))
  have h5 := fusedMultiply_step L hw hn P halfCorrect X (Y/X) cy false origin hX
  have h6 := fastStep_negX L hw hn X Y false origin cx
  have back : Y/X*X=Y := div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,if_true,Nat.cast_zero,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6
  rw [back] at h5
  have h := ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6
  simpa only [generic,fusedMultiply,List.append_assoc] using h
end Correct
end ECDSAAdd.Entrant.All12Generic
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.All12Generic
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
    (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (2^163-1 : Nat) else 0)) Y G origin))
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
end ECDSAAdd.Entrant.All12Generic


-- ALL12 COMPONENT All12Properties
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.All12Generic
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


theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (D : Fp→Program) (S P : Program)
    (hD : ∀k,wires (D k)⊆(OB5Support.sites L).toFinset)
    (hS : wires S⊆(OB5Support.sites L).toFinset)
    (hP : wires P⊆(OB5Support.sites L).toFinset) (cx cy : Fp) :
    wires (generic L D S P cx cy)⊆(OB5Support.sites L).toFinset := by
  have ca : wires (fastConstAdd L L.point.x (-cx)) ⊆ (OB5Support.sites L).toFinset := (add_palette L hw (-cx)).trans
    (finConst_sites L hw L.point.x (Or.inl rfl))
  have cr : wires (fastConstAdd L L.point.x (3*cx-(2^163-1 : Nat))) ⊆ (OB5Support.sites L).toFinset := (add_palette L hw (3*cx-(2^163-1 : Nat))).trans
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
  have cr := FastConst.fastAdd_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) SquareReduction.c (3*cx-(2^163-1 : Nat)).val
  have cn := FastConst.fastNeg_physical
    (L.recoveryConstant_nodup hw hn L.point.x (Or.inl rfl)) p cx.val
  have ey := exitY_physical L hw hn cy
  simp only [generic,fastConstAdd,fastConstNeg,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨ca,hD (-cy)⟩,hS⟩,cr⟩,hP⟩,ey⟩,cn⟩


theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (D : Fp→Program) (S P : Program) (k : Nat) (hk : 515≤k ∧ k<2613)
    (hD : ∀c,L.core.poolWire k∉wires (D c))
    (hS : L.core.poolWire k∉wires S) (hP : L.core.poolWire k∉wires P)
    (cx cy : Fp) : L.core.poolWire k∉wires (generic L D S P cx cy) := by
  have x := ExitGenericQ5.constant_ports_avoid_large L hw hn k hk L.point.x (Or.inl rfl)
  have y := ExitGenericQ5.constant_ports_avoid_large L hw hn k hk L.point.y (Or.inr rfl)
  have ca := (add_palette L hw (-cx))
  have cr := (add_palette L hw (3*cx-(2^163-1 : Nat)))
  have cn := (neg_palette L hw cx)
  have ey := exitY_support L hw cy
  simp only [generic,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨⟨⟨⟨fun h=>x (ca h),hD (-cy)⟩,hS⟩,fun h=>x (cr h)⟩,hP⟩,
    fun h=>y (ey h)⟩,fun h=>x (cn h)⟩

theorem gen_shape (L : ControlledPointLayout) (D : Fp→Program) (S P : Program) (cx cy : Fp) :
    gen L D S P cx cy=GenericQ5Geometry.wrapG L (generic L D S P cx cy) := by
  simp only [gen,mid,GenericQ5Geometry.wrapG]


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


end ECDSAAdd.Entrant.All12Generic


-- ALL12 COMPONENT All12Slots
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.All12Generic
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
  ExitFusionResearch
attribute [local irreducible] fastConstAdd fastConstNeg exitY

theorem generic_slots_le (L : ControlledPointLayout) (hw : L.Widths)
    (D : Fp → Program) (S P : Program)
    (hD : ∀k,gateSlots (D k) ≤ 20525006)
    (hS : gateSlots S ≤ 8000000) (hP : gateSlots P ≤ 20500006) (cx cy : Fp) :
    gateSlots (generic L D S P cx cy) ≤ 49100000 := by
  have add (k : Fp) : gateSlots (fastConstAdd L L.point.x k) ≤ 15368 := by
    simpa only [fastConstAdd] using FastConst.fastAdd_gateSlots_le
      (g:=L.core.generic) 256 SquareReduction.c k.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have neg : gateSlots (fastConstNeg L cx) ≤ 17928 := by
    simpa only [fastConstNeg] using FastConst.fastNeg_gateSlots_le
      (g:=L.core.generic) 256 p cx.val
      (L.recoveryConstant_widths hw L.point.x hw.inputX)
  have a := add (-cx)
  have b := add (3*cx-(2^163-1 : Nat))
  have d := hD (-cy)
  have e := exitY_slots L hw cy
  simp only [generic,gateSlots_append]
  omega

theorem gen_slots_le (L : ControlledPointLayout) (hw : L.Widths)
    (D : Fp → Program) (S P : Program)
    (hD : ∀k,gateSlots (D k) ≤ 20525006)
    (hS : gateSlots S ≤ 8000000) (hP : gateSlots P ≤ 20500006) (cx cy : Fp) :
    gateSlots (gen L D S P cx cy) ≤ 49200000 := by
  have g := generic_slots_le L hw D S P hD hS hP cx cy
  have z := zrep_gateSlots_le L hw
  have c := clrF_gateSlots_le L hw
  simp only [gen,mid,gateSlots_append,rename_gateSlots]
  omega

/-- The actual Q6 entry provider, including its affine entry conversion. -/
theorem actual_division_slots (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    gateSlots (OwnEntryFuseQ6.fusedDivisionF L k) ≤ 20525006 := by
  have d := OwnEntryFuseQ6.arithEntryS_gateSlots_le L
  have y := entry_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)
  simpa only [OwnEntryFuseQ6.fusedDivisionF,EntryFuse.fusedY,gateSlots_append] using
    Nat.add_le_add y d
end ECDSAAdd.Entrant.All12Generic


-- ALL12 COMPONENT All12Counts
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.All12Generic
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
  ExitFusionResearch
attribute [local irreducible] toffoliCount measurementCount generic ExitGenericQ6.generic

theorem square_counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (OwnAll12PlacedQ6.program L)+256=toffoliCount (Q6SquareHost.program L) ∧
    measurementCount (OwnAll12PlacedQ6.program L)+255=measurementCount (Q6SquareHost.program L) := by
  have n:=OwnAll12PlacedQ6.counts L hw
  have a:=Q6SquareHost.counts L
  have b:=SquareOB5.counts L hw
  simp only [SquareOB5.program] at b
  norm_num [lowkcost2] at n
  constructor <;> omega

theorem generic_counts_diff (L : ControlledPointLayout) (hw : L.Widths)
    (D : Fp→Program) (S P : Program)
    (hS : toffoliCount S+256=toffoliCount (Q6SquareHost.program L) ∧
      measurementCount S+255=measurementCount (Q6SquareHost.program L)) (cx cy : Fp) :
    toffoliCount (generic L D S P cx cy)+256=
      toffoliCount (ExitGenericQ6.generic L D (Q6SquareHost.program L) P cx cy) ∧
    measurementCount (generic L D S P cx cy)+255=
      measurementCount (ExitGenericQ6.generic L D (Q6SquareHost.program L) P cx cy) := by
  have a:=fastConstAdd_counts L hw L.point.x (Or.inl rfl) (3*cx-(2^163-1 : Nat))
  have b:=fastConstRefl_counts L hw (3*cx-1)
  simp only [generic,ExitGenericQ6.generic,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem gen_counts_diff (L : ControlledPointLayout) (hw : L.Widths)
    (D : Fp→Program) (S P : Program)
    (hS : toffoliCount S+256=toffoliCount (Q6SquareHost.program L) ∧
      measurementCount S+255=measurementCount (Q6SquareHost.program L)) (cx cy : Fp) :
    toffoliCount (gen L D S P cx cy)+256=
      toffoliCount (ExitGenericQ6.gen L D (Q6SquareHost.program L) P cx cy) ∧
    measurementCount (gen L D S P cx cy)+255=
      measurementCount (ExitGenericQ6.gen L D (Q6SquareHost.program L) P cx cy) := by
  have h:=generic_counts_diff L hw D S P hS cx cy
  simp only [gen,mid,ExitGenericQ6.gen,ExitGenericQ6.mid,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  constructor <;> omega
end ECDSAAdd.Entrant.All12Generic


-- ALL12 COMPONENT All12Producer
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnAll12Producer
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run fastConstAdd fastConstNeg fastConstRefl ExitFusionResearch.exitY

def genericE (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.generic L (OwnEntryFuseQ6.fusedDivisionF L) (OwnAll12PlacedQ6.program L)
    (OwnExitFuseQ6.arithExit L) cx cy

def genE (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.gen L (OwnEntryFuseQ6.fusedDivisionF L) (OwnAll12PlacedQ6.program L)
    (OwnExitFuseQ6.arithExit L) cx cy



theorem square_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (OwnAll12PlacedQ6.program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (2^163-1 : Nat) else 0)) Y G origin) := by
  have h:=OwnAll12PlacedQ6.correct L hw hn X Y G origin
  cases G <;> simpa only [OwnAll12Square.cFlipK,Bool.false_eq_true,if_false,if_true,Nat.cast_zero] using h

theorem genericE_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genericE L cx cy)+256=toffoliCount (OwnQ6Producer.genericE L cx cy) ∧
    measurementCount (genericE L cx cy)+255=measurementCount (OwnQ6Producer.genericE L cx cy) :=
  All12Generic.generic_counts_diff L hw _ _ _ (All12Generic.square_counts_diff L hw) cx cy

theorem genE_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (genE L cx cy)+256=toffoliCount (OwnQ6Producer.genE L cx cy) ∧
    measurementCount (genE L cx cy)+255=measurementCount (OwnQ6Producer.genE L cx cy) :=
  All12Generic.gen_counts_diff L hw _ _ _ (All12Generic.square_counts_diff L hw) cx cy

theorem genE_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (genE L cx cy)≤49200000 :=
  All12Generic.gen_slots_le L hw _ _ _ (All12Generic.actual_division_slots L hw)
    (OwnAll12PlacedQ6.slots L hw) ((OwnExitFuseQ6.arithExit_slots_le L).trans (by decide)) cx cy


theorem genericE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (genericE L cx cy)⊆(OB5Support.sites L).toFinset :=
  All12Generic.generic_sites L hw _ _ _ (Q6ComponentSupport.division_support L hw)
    (OwnAll12PlacedQ6.support L hw hn) (OwnExitFuseQ6.arithExit_support L hw) cx cy

theorem genE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (genE L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [genE,All12Generic.gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (genericE_sites L hw hn cx cy)

theorem genE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    GatePhysical (genE L cx cy) :=
  All12Generic.gen_physical L hw hn _ _ _ (Q6ComponentSupport.division_physical L hw hn)
    (OwnAll12PlacedQ6.physical L hw hn) (OwnExitFuseQ6.arithExit_physical L hw hn) cx cy


theorem genericE_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) (cx cy : Fp) :
    L.core.poolWire k∉wires (genericE L cx cy) := by
  have bounds:515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  exact All12Generic.generic_free L hw hn _ _ _ k bounds
    (Q6ComponentSupport.division_free L hw hn entryFree k hk)
    (OwnAll12PlacedQ6.square_free L hw hn k hk)
    (Q6FusionOmissions.exit_avoids L hw hn exitFree k hk) cx cy

theorem genE_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base)) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (genE L cx cy) :=
  All12Generic.genFFused_ok L hw hn _ _ _
    (OwnExitFuseQ6.arithExit_correct exitFree L hw hn)
    (OwnEntryFuseQ6.fusedDivisionF_step entryFree L hw hn logicalND hlo logicalAway logicalReplay)
    (square_step L hw hn) hc
end ECDSAAdd.Entrant.OwnAll12Producer


-- ALL12 COMPONENT All12Inventory
namespace ECDSAAdd.Entrant.OwnAll12Producer
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite

theorem genE_qubits1593
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS) (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (genE layout cx cy))≤1593 := by
  rw [genE,All12Generic.gen_shape]
  apply GenericQ6Geometry.edges_wrapG_qubits _ (genericE_sites layout layout_widths layout_nodup cx cy)
  · intro k hk
    exact genericE_free layout layout_widths layout_nodup entryFree
      exitFree k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with h|h|h|h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) cx cy
  · exact genericE_free layout layout_widths layout_nodup entryFree
      exitFree 1285 (by simp) cx cy
end ECDSAAdd.Entrant.OwnAll12Producer


-- ALL12 COMPONENT All12Final
namespace ECDSAAdd.Entrant.All12CurrentCertificate
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (OwnAll12Producer.genE layout cx cy)
def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2155226,1500944,1593,50000004⟩

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
    have hG:=OwnAll12Producer.genE_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (OwnAll12Producer.genE_ok layout layout_widths layout_nodup OwnQ6Actual.entry_selected_free
          OwnQ6Actual.exit_selected_free cfg.1 above cfg.2.1 cfg.2.2 hc) hG)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ hG).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2155226 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have h:=(Edges.wrapper_counts layout layout_widths (OwnAll12Producer.genE layout cx cy) hc).1
    have g:=(SelGeneric5.program_counts layout layout_widths cx cy).1
    have gf:=(genF_counts layout layout_widths cx cy).1
    have gd:=(genFFused_counts_diff layout layout_widths cx cy).1
    have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).1
    have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).1
    have ga:=(OwnAll12Producer.genE_counts_diff layout layout_widths cx cy).1
    change toffoliCount (Edges.wrapper layout (.some hc) cy (OwnAll12Producer.genE layout cx cy))≤2155226
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1500944 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have h:=(Edges.wrapper_counts layout layout_widths (OwnAll12Producer.genE layout cx cy) hc).2
    have g:=(SelGeneric5.program_counts layout layout_widths cx cy).2
    have gf:=(genF_counts layout layout_widths cx cy).2
    have gd:=(genFFused_counts_diff layout layout_widths cx cy).2
    have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).2
    have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).2
    have ga:=(OwnAll12Producer.genE_counts_diff layout layout_widths cx cy).2
    change measurementCount (Edges.wrapper layout (.some hc) cy (OwnAll12Producer.genE layout cx cy))≤1500944
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1593 := by
  cases C with
  | zero => change qubits []≤1593;rw [qubits_empty];decide
  | @some cx cy hc => exact OwnAll12Producer.genE_qubits1593 OwnQ6Actual.entry_selected_free OwnQ6Actual.exit_selected_free (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (OwnAll12Producer.genE_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50000004 := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc =>
    have h:=Edges.wrapper_slots layout layout_widths (.some hc) cy (OwnAll12Producer.genE layout cx cy)
    have g:=OwnAll12Producer.genE_gateSlots_le layout layout_widths cx cy
    change gateSlots (Edges.wrapper layout (.some hc) cy (OwnAll12Producer.genE layout cx cy))≤_
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1500944
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1593
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50000004
    rw [normalize_slots];exact program_gateSlots C
end ECDSAAdd.Entrant.All12CurrentCertificate

