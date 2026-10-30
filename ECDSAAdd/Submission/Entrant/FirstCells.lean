import ECDSAAdd.Submission.Entrant.JointEntry
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.FirstQLoan
open Arithmetic Secp256k1 BalancedField MappedCompressed Challenge Baselines RecordedQuantum
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def trits (i : Fin 6) : Wire :=
  if i.val%2=0 then base (2+i.val/2) else base (1030+i.val/2)

theorem trits_injective : Function.Injective trits := by decide +kernel
theorem trits_above : ∀i,6≤trits i := by decide +kernel

def unPack : Program := renameProgram (TranscriptCodec3.placement trits) TranscriptCodec3.unpack
def pack : Program := unPack.reverse
def virtual : Program := FirstInvReplay.joint1592
def borrow : Equiv.Perm Wire := Equiv.swap (base 1540) (base 1031)
def program : Program := pack ++ renameProgram borrow virtual ++ unPack
attribute [local irreducible] virtual

theorem unPack_proper : ProperProgram unPack := by
  have h : ProperProgram TranscriptCodec3.unpack := by
    simp [ProperProgram,TranscriptCodec3.unpack,ProperGate]
  intro i hi
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi
  have hp:=h j hj
  cases j with
  | X a => trivial
  | CX a b => exact fun eq => hp ((TranscriptCodec3.placement trits).injective eq)
  | CCX a b c => exact ⟨fun eq=>hp.1 ((TranscriptCodec3.placement trits).injective eq),
      fun eq=>hp.2 ((TranscriptCodec3.placement trits).injective eq)⟩
  | measureX q c0 c1 => exact False.elim hp

theorem pack_proper : ProperProgram pack := properProgram_reverse _ unPack_proper

theorem counts : toffoliCount unPack=4 ∧ measurementCount unPack=0 ∧
    toffoliCount pack=4 ∧ measurementCount pack=0 := by
  have h:=TranscriptCodec3.placement_counts trits
  have t:=toffoliCount_reverse unPack
  have m:=measurementCount_reverse unPack
  exact ⟨h.2.2.1,h.2.2.2,t.trans h.2.2.1,m.trans h.2.2.2⟩

theorem unPack_records (s : State) (m : List Bool) : run unPack m s=run unPack [] s := by
  rw [←run_take unPack m s,counts.2.1,List.take_zero]

theorem roundtrip (s : State) (a b : List Bool) : run unPack b (run pack a s)=s := by
  have h:=run_reverse_proper unPack.reverse (properProgram_reverse _ unPack_proper) s a b
  simpa only [List.reverse_reverse,pack] using h

def Legal (s : BasisState) : Prop :=
  (s (trits 0) && s (trits 1))=false ∧
  (s (trits 2) && s (trits 3))=false ∧
  (s (trits 4) && s (trits 5))=false

theorem pack_hole (s : State) (h : Legal s.basis) : (run pack [] s).basis (base 1031)=false := by
  have measured:=TranscriptCodec3.placement_correct trits trits_injective trits_above s [] h
  have rt:=TranscriptCodec3.decode_encode trits trits_injective trits_above s [] [] h
  change run unPack [] (run (TranscriptCodec3.encode trits) [] s)=s at rt
  have inv:=run_reverse_proper unPack unPack_proper (run (TranscriptCodec3.encode trits) [] s) [] []
  have same : run pack [] s=run (TranscriptCodec3.encode trits) [] s :=
    (congrArg (fun z=>run unPack.reverse [] z) rt.symm).trans inv
  rw [same]
  exact measured.2.1

theorem unPack_support : wires unPack=Finset.univ.image trits := by
  rw [unPack,renameProgram_support,TranscriptCodec3.support.2]
  ext q
  simp only [Finset.mem_image,Finset.mem_range,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,hi⟩,(TranscriptCodec3.placement_apply trits trits_injective trits_above ⟨i,hi⟩).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨i.val,i.isLt,TranscriptCodec3.placement_apply trits trits_injective trits_above i⟩

theorem pack_support : wires pack=Finset.univ.image trits := by rw [pack,wires_reverse,unPack_support]

theorem codec_off_carry : base 1540∉wires pack := by
  rw [pack_support]
  simp only [Finset.mem_image,Finset.mem_univ,true_and,not_exists]
  intro i
  fin_cases i <;> simp [trits,base_injective.eq_iff]

def rawSites : Finset Wire := EntryRetained5.retSites FirstInvReplay.loanPorts1592 (base 1028) (base 1) ∪ {base 0}

theorem virtual_support : wires virtual⊆rawSites.erase (base 1541) := by
  rw [virtual]
  have core:=FirstInverse5.programC_support FirstInvReplay.loanPorts1592 FirstInvReplay.loanPorts1592_widths (base 1028) (base 1)
  have flags (q : Wire) (hq : q=base 1028 ∨ q=base 1) : q∈rawSites := by
    rcases hq with rfl|rfl <;> simp [rawSites,EntryRetained5.retSites]
  have x : wires [Instr.X (base 1)]⊆rawSites := by
    intro q hq
    have e:q=base 1:=by simpa [wires,Instr.wires] using hq
    exact flags q (Or.inr e)
  have joint : wires (FirstInverse5.jointInv FirstInvReplay.loanPorts1592 (base 1028) (base 1))⊆rawSites := by
    rw [FirstInverse5.jointInv,wires_append,wires_append]
    exact Finset.union_subset (Finset.union_subset x (core.trans Finset.subset_union_left)) x
  exact FirstInvReplay.joint1592_support _ joint (flags _ (Or.inl rfl)) (by simp [rawSites])

theorem virtual_codec_disjoint : Disjoint (wires virtual) (wires pack) := by
  apply Finset.disjoint_left.mpr
  intro q hp he
  have p:=Finset.mem_of_mem_erase (virtual_support hp)
  rw [pack_support] at he
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
  simp only [rawSites,EntryRetained5.retSites,FirstInvReplay.loanPorts1592,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    Finset.mem_union,Finset.mem_singleton,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at p
  have carry : trits i∉(wireBlock base 512 253++[base 1540,base 1541,base 1026]).take 255 := by
    intro h
    have hh:=List.mem_of_mem_take h
    fin_cases i <;> simp [trits,wireBlock,List.mem_range'_1,base_injective.eq_iff] at hh
  have regions : trits i∉[base 2056]++(wireBlock base 2057 254++[base 2311]) ∧
      trits i∉wireBlock base 770 255++[base 1025] := by
    fin_cases i <;> simp [trits,wireBlock,List.mem_range'_1,base_injective.eq_iff]
  have flags : trits i≠base 768 ∧ trits i≠base 1797 ∧ trits i≠base 1027 ∧
      trits i≠base 2409 ∧ trits i≠base 1028 ∧ trits i≠base 1 ∧ trits i≠base 0 := by
    fin_cases i <;> simp [trits,base_injective.eq_iff]
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at regions
  tauto

theorem virtual_off_hole : base 1031∉wires virtual := by
  intro h
  apply Finset.disjoint_left.mp virtual_codec_disjoint h
  rw [pack_support]
  exact Finset.mem_image.mpr ⟨(3 : Fin 6),Finset.mem_univ _,rfl⟩

def sequence (E D P : Program) (c h : Wire) : Program :=
  E++renameProgram (Equiv.swap c h) P++D

theorem sequence_eq (E D P : Program) (c h : Wire)
    (em : measurementCount E=0) (dm : measurementCount D=0)
    (rt : ∀t,run D [] (run E [] t)=t)
    (sep : Disjoint (wires P) (wires E)) (ec : c∉wires E) (ph : h∉wires P)
    (s : State) (m : List Bool) (hz : (run E [] s).basis h=false)
    (cin : s.basis c=false) (cout : (run P m s).basis c=false) :
    run (sequence E D P c h) m s=run P m s := by
  let a:=run E [] s
  have c0:a.basis c=false := (run_preserves_outside E [] s c ec).trans cin
  have comm:=run_disjoint_commute P E sep m [] s
  have c1:(run P m a).basis c=false := by
    rw [comm,run_preserves_outside E [] (run P m s) c ec]
    exact cout
  have h1:(run P m a).basis h=false := (run_preserves_outside P m a h ph).trans hz
  have rebound:=G0CarryLoan5.rebind_swap_run c h P a m c0 hz c1 h1
  have records (t : State) (r : List Bool) : run D r t=run D [] t := by
    rw [←run_take D r t,dm,List.take_zero]
  have shape : run (sequence E D P c h) m s=
      run D [] (run (renameProgram (Equiv.swap c h) P) m a) := by
    rw [sequence,List.append_assoc,run_append,em,List.take_zero,List.drop_zero,
      run_append,run_take,records]
  rw [shape,rebound,comm]
  exact rt _

theorem program_eq (s : State) (m : List Bool) (legal : Legal s.basis)
    (cin : s.basis (base 1540)=false) (cout : (run virtual m s).basis (base 1540)=false) :
    run program m s=run virtual m s := by
  have generic:=sequence_eq pack unPack virtual (base 1540) (base 1031)
    counts.2.2.2 counts.2.1 (fun t=>roundtrip t [] []) virtual_codec_disjoint codec_off_carry
    virtual_off_hole s m (pack_hole s legal) cin cout
  have shape:program=sequence pack unPack virtual (base 1540) (base 1031) := by
    rw [program,sequence,borrow]
  exact (congrArg (fun P:Program=>run P m s) shape).trans generic

theorem ports_nodup : FirstInvReplay.loanPorts1592.wires.Nodup := by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have hs : base 2409∉Q6EndpointCell.ids.map base := by
    intro used
    exact cfg.2.1 (base 2409) (by simp)
      (balancedSharedLayout_mapSubset base Q6EndpointCell.ids Q6EndpointCell.ids_bound used)
  exact Q6EndpointCell.ports_nodup base (base 2409) cfg.1 hs

theorem program_counts : toffoliCount program=523 ∧ measurementCount program=770 := by
  have v:toffoliCount virtual=515 ∧ measurementCount virtual=770 := by
    rw [virtual]
    exact FirstInvReplay.joint1592_counts ports_nodup
  have r:=renameProgram_counts borrow virtual
  simp only [program,toffoliCount_append,measurementCount_append,r.1,r.2,
    counts.1,counts.2.1,counts.2.2.1,counts.2.2.2,v.1,v.2]
  decide

private def gateCheck : Instr → Bool
  | .X _ => true
  | .CX a b => decide (a≠b)
  | .CCX a b c => decide (a≠b ∧ a≠c ∧ b≠c)
  | .measureX _ _ _ => false

private theorem gateCheck_spec (i : Instr) (h : gateCheck i=true) : PhysicalInstr (.gate i) := by
  cases i <;> simp_all [gateCheck,PhysicalInstr,ProperGate]

theorem unPack_physical : GatePhysical unPack := by
  have checked : TranscriptCodec3.unpack.all gateCheck=true := by decide +kernel
  have good : GatePhysical TranscriptCodec3.unpack := by
    intro i hi
    exact gateCheck_spec i ((List.all_eq_true.mp checked) i hi)
  exact gatePhysical_rename _ (TranscriptCodec3.placement trits).injective _ good

theorem pack_physical : GatePhysical pack := by
  intro i hi
  exact unPack_physical i (List.mem_reverse.mp hi)

section ProgramResources
attribute [local irreducible] pack unPack

theorem program_physical : GatePhysical program := by
  have v:GatePhysical virtual := by
    rw [virtual]
    exact FirstInvReplay.joint1592_physical ports_nodup
  rw [program,gatePhysical_append,gatePhysical_append]
  exact And.intro (And.intro pack_physical (gatePhysical_rename _ borrow.injective _ v)) unPack_physical

theorem program_slots : gateSlots program≤10406 := by
  have v:gateSlots virtual≤10006 := by
    rw [virtual]
    exact FirstInvReplay.joint1592_slots ports_nodup
  have u:gateSlots unPack≤200 := by
    rw [unPack,rename_gateSlots]
    decide +kernel
  have rev:gateSlots pack=gateSlots unPack := by
    rw [pack,reverse_gateSlots]
  rw [program,gateSlots_append,gateSlots_append,rename_gateSlots]
  omega

end ProgramResources

theorem trits_away (i : Fin 6) :
    trits i∉FirstInvReplay.loanPorts1592.r ∧ trits i∉FirstInvReplay.loanPorts1592.y := by
  fin_cases i <;> simp [trits,FirstInvReplay.loanPorts1592,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,wireBlock,List.mem_range'_1,base_injective.eq_iff]

theorem carry_away : base 1540∉FirstInvReplay.loanPorts1592.r ∧
    base 1540∉FirstInvReplay.loanPorts1592.y := by
  simp [FirstInvReplay.loanPorts1592,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,wireBlock,List.mem_range'_1,base_injective.eq_iff]

private theorem pair_false (a b : Bool) (h : a.toNat+2*b.toNat<3) : (a&&b)=false := by
  cases a <;> cases b <;> simp_all

theorem legal_of_frame (origin : BasisState) (legal : History5.RawLegal base 102 origin)
    (A B : Nat) (s : State)
    (frame : PairFrame FirstInvReplay.loanPorts1592.r FirstInvReplay.loanPorts1592.y origin A B s.basis) :
    Legal s.basis := by
  have keep (i : Fin 6) : s.basis (trits i)=origin (trits i) :=
    frame.2.2 _ (trits_away i).1 (trits_away i).2
  have raw (k : Nat) (hk : k<5) :
      (origin (base k) && origin (base (1028+k)))=false := by
    apply pair_false
    have h:=(legal 0 (by decide)) k hk
    interval_cases k <;>
      simpa [MeasuredCodec5.pair,MeasuredCodec5.label,History5.historyMap,History5.historyId] using h
  simp only [Legal,keep]
  exact ⟨raw 2 (by decide),raw 3 (by decide),raw 4 (by decide)⟩

theorem carry_clean (origin : BasisState) (env : OffsetBorrowedCanonical.Env base origin) :
    origin (base 1540)=false := by
  apply (regValue_zero _ _).mp env.1
  have member : base 1540∈wireBlock base 1540 257 :=
    List.mem_map.mpr ⟨1540,by simp [List.mem_range'_1],rfl⟩
  simp only [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl member)))

theorem frame (origin : BasisState) (env : OffsetBorrowedCanonical.Env base origin)
    (legal : History5.RawLegal base 102 origin) (A B C D : Nat)
    (v : Triple (PairFrame FirstInvReplay.loanPorts1592.r FirstInvReplay.loanPorts1592.y origin A B) virtual
      (PairFrame FirstInvReplay.loanPorts1592.r FirstInvReplay.loanPorts1592.y origin C D)) :
    Triple (PairFrame FirstInvReplay.loanPorts1592.r FirstInvReplay.loanPorts1592.y origin A B) program
      (PairFrame FirstInvReplay.loanPorts1592.r FirstInvReplay.loanPorts1592.y origin C D) := by
  intro s m input
  have out:=v s m input
  have ci:s.basis (base 1540)=false :=
    (input.2.2 _ carry_away.1 carry_away.2).trans (carry_clean origin env)
  have co:(run virtual m s).basis (base 1540)=false :=
    (out.2.2.2 _ carry_away.1 carry_away.2).trans (carry_clean origin env)
  rw [program_eq s m (legal_of_frame origin legal A B s input) ci co]
  exact out

theorem program_support (W : Finset Wire) (hr : rawSites⊆W)
    (hc : base 1540∈W) (ht : ∀i,trits i∈W) : wires program⊆W := by
  have v : wires virtual⊆W := virtual_support.trans ((Finset.erase_subset _ _).trans hr)
  have mapped : wires (renameProgram borrow virtual)⊆W := by
    rw [renameProgram_support]
    intro q hq
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hq
    by_cases ac:a=base 1540
    · subst a
      simpa only [borrow,Equiv.swap_apply_left] using ht 3
    · by_cases ah:a=base 1031
      · subst a
        simpa only [borrow,Equiv.swap_apply_right] using hc
      · simpa only [borrow,Equiv.swap_apply_of_ne_of_ne ac ah] using v ha
  have u : wires unPack⊆W := by
    rw [unPack_support]
    intro q hq
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hq
    exact ht i
  have p : wires pack⊆W := by rwa [pack_support,←unPack_support]
  rw [program,wires_append,wires_append]
  exact Finset.union_subset (Finset.union_subset p mapped) u

def Bad : List Nat := [765,766,767,2312,1026,1540,1541,1542,1539,2400,2410,511]

theorem carry_take : FirstInvReplay.loanPorts1592.carry.take 255=
    wireBlock base 512 253++[base 1540,base 1541] := by
  change (wireBlock base 512 253++[base 1540,base 1541,base 1026]).take 255=_
  rw [List.take_append]
  simp only [wireBlock_length,Nat.reduceSub]
  rw [List.take_of_length_le (by simp only [wireBlock_length];omega)]
  rfl

theorem raw_free (q : Nat) (hq : q∈Bad) (c : q≠1540) (d : q≠1541) : base q∉rawSites := by
  intro used
  rw [rawSites,EntryRetained5.retSites,carry_take] at used
  simp only [FirstInvReplay.loanPorts1592,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    Finset.mem_union,Finset.mem_singleton,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,wireBlock,List.mem_map,List.mem_range'_1,base_injective.eq_iff] at used
  simp only [Bad,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [or_assoc] at used
  rcases used with u|⟨i,hi,eq⟩|u|⟨i,hi,eq⟩|u|⟨i,hi,eq⟩|u|u|u|u|u|u|u|u|u
  all_goals omega

theorem codec_free (q : Nat) (hq : q∈Bad) : base q∉wires unPack ∧ base q∉wires pack := by
  have off : base q∉Finset.univ.image trits := by
    intro used
    obtain ⟨i,_,eq⟩:=Finset.mem_image.mp used
    have small : (2≤q ∧ q≤4) ∨ (1030≤q ∧ q≤1032) := by
      fin_cases i <;> simp [trits,base_injective.eq_iff] at eq <;> omega
    simp only [Bad,List.mem_cons,List.not_mem_nil,or_false] at hq
    omega
  exact ⟨by rwa [unPack_support],by rwa [pack_support]⟩

theorem rebound_free (q : Nat) (hq : q∈Bad) : base q∉wires (renameProgram borrow virtual) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨a,ha,eq⟩:=Finset.mem_image.mp used
  have back:a=borrow (base q) := by
    have h:=congrArg borrow eq
    simpa only [borrow,Equiv.swap_apply_self] using h
  rw [back] at ha
  by_cases qc:q=1540
  · subst q
    rw [borrow,Equiv.swap_apply_left] at ha
    exact virtual_off_hole ha
  have notHole:q≠1031 := by
    simp only [Bad,List.mem_cons,List.not_mem_nil,or_false] at hq
    omega
  have cneq:base q≠base 1540:=fun h=>qc (base_injective h)
  have hneq:base q≠base 1031:=fun h=>notHole (base_injective h)
  rw [borrow,Equiv.swap_apply_of_ne_of_ne cneq hneq] at ha
  by_cases qd:q=1541
  · subst q
    exact (Finset.mem_erase.mp (virtual_support ha)).1 rfl
  exact raw_free q hq qc qd (Finset.mem_of_mem_erase (virtual_support ha))

theorem program_free (q : Nat) (hq : q∈Bad) : base q∉wires program := by
  simp only [program,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨(codec_free q hq).2,rebound_free q hq⟩,(codec_free q hq).1⟩

end ECDSAAdd.Entrant.FirstQLoan
