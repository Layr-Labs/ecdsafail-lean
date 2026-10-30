import ECDSAAdd.Submission.Entrant.NewFieldFrameOB5

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.NewHalfField5
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport
open OffsetBorrowedCanonical RecordedQuantum NewHistory5
attribute [local irreducible] run wires NewHistory5.allEncode

abbrev tgt := HalfField.tgt
abbrev ports := HalfField.ports
abbrev centerT := HalfField.centerT
abbrev canonT := HalfField.canonT
abbrev copyN := HalfField.copyN
abbrev ids := HalfField.ids

private theorem ports_r : ports.r=wireBlock base 2056 256 := balancedSharedPorts_r base (base 2409)
private theorem ports_y : ports.y=wireBlock base 770 256 := balancedSharedPorts_y base (base 2409)

theorem encoder_disjoint (P : Program) (h : wires P⊆(ids.map base).toFinset) :
    Disjoint (wires (NewHistory5.allEncode base 102)) (wires P) := by
  have hist := NewHistory5.allEncode_history_support base 102 (by decide)
  apply Finset.disjoint_left.mpr
  intro q hq hc
  have history := List.mem_toFinset.mp (hist hq)
  have converted := List.mem_toFinset.mp (h hc)
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp converted
  simp only [List.mem_append,wireBlock] at history
  rcases history with history|history
  all_goals
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp history
    have same := base_injective eq
    subst i
    simp only [List.mem_range'_1] at hi
    simp only [ids,HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
    omega

private theorem centerT_sites : wires centerT⊆(ids.map base).toFinset := HalfField.centerT_sites
private theorem canonT_sites : wires canonT⊆(ids.map base).toFinset := HalfField.canonT_sites
private theorem copyN_sites : wires copyN⊆(ids.map base).toFinset := HalfField.copyN_sites

private theorem xor_neutral (a b : Bool) (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem encoded_transport (P : Program) (dis : Disjoint (wires (NewHistory5.allEncode base 102)) (wires P))
    (s raw : State) (m : List Bool) (encoded : s=run (NewHistory5.allEncode base 102) [] raw)
    (phase : (run P m raw).phase=raw.phase) :
    (run P m s).phase=s.phase ∧ run P m s=run (NewHistory5.allEncode base 102) [] (run P m raw) := by
  have read : ∀q∈wires P,s.basis q=raw.basis q := by
    intro q hq
    rw [encoded]
    exact run_preserves_outside _ [] raw q (fun he => Finset.disjoint_left.mp dis he hq)
  have increment := (run_local_increment P s raw m read).1
  rw [phase,Bool.xor_self] at increment
  refine ⟨xor_neutral _ _ increment,?_⟩
  rw [encoded]
  exact (run_disjoint_commute _ _ dis [] m raw).symm

/-! Frame steps. -/

private theorem port_split :
    (skywalkSharedField base).z=ports.r++[base 2312] ∧
    (skywalkSharedField base).a=ports.y++[base 1026] := by
  rw [skywalkShared_field_z,ports_r,ports_y]
  constructor
  · have split := wireBlock_append base 2056 256 1
    simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using split.symm
  · have split := wireBlock_append base 770 256 1
    simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using split.symm

private theorem value_bound (X : Fp) : X.val<2^256 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact (ZMod.val_lt X).trans (by norm_num [p])

theorem centerWord_zero : centerWord (0:Fp)=0 := by
  have h : (0:Int)≤q := by norm_num [q,p]
  simp [centerWord,centerFp,encodeWord,h]

private theorem target_clean (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0) (A B : Nat) (st : BasisState)
    (frame : PairFrame ports.r ports.y origin A B st) :
    ∀q∈BalancedConvert.work tgt,st q=false := by
  have clean := balancedSharedBoundary_clean base (base 2409) origin hw hu
  have away := (balancedSharedBoundary base (base 2409) hn).targetWorkAway
  intro q hq
  exact (frame.2.2 q (away q hq).1 (away q hq).2).trans (clean.1 q hq)

private theorem pair_dis (hn : (skywalkSharedWires base).Nodup) : ports.r.Disjoint ports.y :=
  (List.nodup_append'.mp (balancedSharedLayout_pairND base (base 2409) hn)).2.2

private theorem tgt_word : tgt.word=ports.r := balancedSharedTargetConvert_word base (base 2409)

private theorem center_frame_generic (P : Program)
    (sites : wires P⊆(ids.map base).toFinset) (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame5 origin X 0 s)
    (hcorrect : ∀ (raw : State) (records : List Bool),
      regValue tgt.word raw.basis=X.val →
      (∀q∈BalancedConvert.work tgt,raw.basis q=false) →
      let z := run P records raw
      z.phase=raw.phase ∧ regValue tgt.word z.basis=centerWord (X/2) ∧
      (∀q∈BalancedConvert.work tgt,z.basis q=false) ∧
      (∀q,q∉tgt.word → z.basis q=raw.basis q)) :
    (run P m s).phase=s.phase ∧
    EncodedFieldFrame5 base (base 2409) origin (X/2) 0 (run P m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have split := port_split
  rw [split.1,split.2,ZMod.val_zero] at frame
  have narrow := balancedPair_narrow ports.r ports.y (base 2312) (base 1026) origin raw.basis
    X.val 0 (by rw [ports_r,wireBlock_length]; exact value_bound X)
    (by rw [ports_y,wireBlock_length]; norm_num) frame hr hy
  have c := hcorrect raw m (by rw [tgt_word]; exact narrow.1)
    (target_clean hn origin hw hu _ _ _ narrow)
  have pf : PairFrame ports.r ports.y origin (centerWord (X/2)) (centerWord 0)
      (run P m raw).basis := by
    rw [centerWord_zero]
    exact PairFrame.update_temp ports.r ports.y origin raw.basis _ X.val 0 _ (pair_dis hn) narrow
      (by rw [←tgt_word]; exact c.2.2.2) (by rw [←tgt_word]; exact c.2.1)
  have actual := encoded_transport P (encoder_disjoint _ sites) s raw m encoded c.1
  exact ⟨actual.1,run P m raw,c.1.trans (phase.trans actual.1.symm),pf,actual.2⟩


/-- Halving entry conversion of the target port; the zero source port is
already its own balanced word. -/
theorem center_frame (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame5 origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    EncodedFieldFrame5 base (base 2409) origin (X/2) 0 (run centerT m s) := by
  exact center_frame_generic centerT centerT_sites hn origin hw hu hr hy X s m input
    (HalfConvert.center_correct tgt (balancedSharedTargetConvert_widths base)
      (balancedSharedTargetConvert_nodup base hn) X)


private theorem canon_frame_generic (P : Program)
    (sites : wires P⊆(ids.map base).toFinset) (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame5 base (base 2409) origin X 0 s)
    (hcorrect : ∀ (raw : State) (records : List Bool),
      regValue tgt.word raw.basis=centerWord X →
      (∀q∈BalancedConvert.work tgt,raw.basis q=false) →
      let z := run P records raw
      z.phase=raw.phase ∧ regValue tgt.word z.basis=(2*X).val ∧
      (∀q∈BalancedConvert.work tgt,z.basis q=false) ∧
      (∀q,q∉tgt.word → z.basis q=raw.basis q)) :
    (run P m s).phase=s.phase ∧ EncodedCanonicalFrame5 origin (2*X) 0 (run P m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  rw [centerWord_zero] at frame
  have c := hcorrect raw m (by rw [tgt_word]; exact frame.1)
    (target_clean hn origin hw hu _ _ _ frame)
  have pf : PairFrame ports.r ports.y origin (2*X).val 0 (run P m raw).basis :=
    PairFrame.update_temp ports.r ports.y origin raw.basis _ _ 0 _ (pair_dis hn) frame
      (by rw [←tgt_word]; exact c.2.2.2) (by rw [←tgt_word]; exact c.2.1)
  have outside := balancedSharedDivision_high_outside base hn
  have wide := balancedPair_widen ports.r ports.y (base 2312) (base 1026) origin _ (2*X).val 0 pf
    (by rw [ports_r,ports_y]; exact outside.1) (by rw [ports_r,ports_y]; exact outside.2) hr hy
  have split := port_split
  rw [←split.1,←split.2] at wide
  have actual := encoded_transport P (encoder_disjoint _ sites) s raw m encoded c.1
  refine ⟨actual.1,run P m raw,c.1.trans (phase.trans actual.1.symm),?_,actual.2⟩
  rw [ZMod.val_zero]
  exact wide


/-- Doubling exit conversion of the target port; the zero source port is
already canonical. -/
theorem canon_frame (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame5 base (base 2409) origin X 0 s) :
    (run canonT m s).phase=s.phase ∧ EncodedCanonicalFrame5 origin (2*X) 0 (run canonT m s) := by
  exact canon_frame_generic canonT canonT_sites hn origin hw hu hr hy X s m input
    (HalfConvert.canonical_correct tgt (balancedSharedTargetConvert_widths base)
      (balancedSharedTargetConvert_nodup base hn) X)


private theorem copy_raw (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (A B : Nat) (raw : State) (m : List Bool)
    (frame : PairFrame ports.r ports.y origin A B raw.basis) :
    (run copyN m raw).phase=raw.phase ∧
    PairFrame ports.r ports.y origin A (B ^^^ A) (run copyN m raw).basis := by
  have len : ports.r.length=ports.y.length := by rw [ports_r,ports_y]; simp [wireBlock_length]
  obtain ⟨phase,keep,value⟩ := copyRegister_correct none ports.r ports.y len
    (balancedSharedLayout_pairND base (base 2409) hn) (by simp) raw m
  refine ⟨phase,PairFrame.update_dst _ _ origin raw.basis _ A B _ (pair_dis hn) frame keep ?_⟩
  simpa only [copyValue,frame.1,frame.2.1] using value

/-- Duplicate the balanced target into the clean source. -/
theorem copy_fill (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame5 base (base 2409) origin X 0 s) :
    (run copyN m s).phase=s.phase ∧ EncodedFieldFrame5 base (base 2409) origin X X (run copyN m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have c := copy_raw hn origin _ _ raw m frame
  rw [centerWord_zero,Nat.zero_xor] at c
  have actual := encoded_transport copyN (encoder_disjoint _ copyN_sites) s raw m encoded c.1
  exact ⟨actual.1,run copyN m raw,c.1.trans (phase.trans actual.1.symm),c.2,actual.2⟩

/-- Clear the source against the equal balanced target. -/
theorem copy_clear (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame5 base (base 2409) origin X X s) :
    (run copyN m s).phase=s.phase ∧ EncodedFieldFrame5 base (base 2409) origin X 0 (run copyN m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  have c := copy_raw hn origin _ _ raw m frame
  rw [Nat.xor_self,←centerWord_zero] at c
  have actual := encoded_transport copyN (encoder_disjoint _ copyN_sites) s raw m encoded c.1
  exact ⟨actual.1,run copyN m raw,c.1.trans (phase.trans actual.1.symm),c.2,actual.2⟩


theorem encoder_pool_support :
    wires (NewHistory5.allEncode base 102)⊆(skywalkPoolWires base).toFinset := by
  intro q hq
  have member := List.mem_toFinset.mp (NewHistory5.allEncode_history_support base 102 (by decide) hq)
  simp only [List.mem_append,wireBlock] at member
  rcases member with member|member
  all_goals
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    simp only [List.mem_range'_1] at hi
    apply List.mem_toFinset.mpr
    simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨i,by omega,rfl⟩

theorem encodedCanonical_pool_basis5 (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame5 origin X 0 s) :
    ∀q∈skywalkPoolWires base,s.basis q=
      (run (NewHistory5.allEncode base 102) [] ({phase:=false,basis:=origin} : State)).basis q := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have narrow : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
      origin X.val 0 raw.basis := by simpa only [ZMod.val_zero] using rawFrame
  exact encoded_field_pool_basis base hn (NewHistory5.allEncode base 102) encoder_pool_support origin ha
    X.val raw s narrow encoded

theorem encodedCanonical_caller_frame5 (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame5 origin X 0 s) :
    regValue (skywalkSharedField base).z s.basis=X.val ∧
    ∀q,q∉(skywalkSharedField base).z → q∉skywalkPoolWires base → s.basis q=origin q := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have narrow : PairFrame (skywalkSharedField base).z (skywalkSharedField base).a
      origin X.val 0 raw.basis := by simpa only [ZMod.val_zero] using rawFrame
  have keeps := DirectSkywalk.arith_field_frame (skywalkSharedField base) origin raw.basis X.val ha narrow
  have away (q : Wire) (hq : q∉skywalkPoolWires base) :
      (run (NewHistory5.allEncode base 102) [] raw).basis q=raw.basis q :=
    run_preserves_outside _ [] raw q (fun used => hq (List.mem_toFinset.mp (encoder_pool_support used)))
  constructor
  · apply Eq.trans (regValue_congr _ _ _ ?_) narrow.1
    intro q hq
    rw [encoded]
    exact away q (fun hp => DirectSkywalk.arith_pool_away_z base hn q hp hq)
  · intro q hz hp
    rw [encoded]
    exact (away q hp).trans (keeps q hz)

end ECDSAAdd.Entrant.NewHalfField5

namespace ECDSAAdd.Entrant.NewHalfFieldOB5
open Arithmetic Secp256k1 BalancedField MappedCompressed OffsetBorrowedCanonical NewHistory5
attribute [local irreducible] run wires NewHistory5.allEncode

private def bankFn (i : Nat) : Nat :=
  if 512 ≤ i ∧ i < 767 then i+1028 else if 1540 ≤ i ∧ i < 1795 then i-1028 else i

private theorem bank_invol : Function.Involutive bankFn := by
  intro i
  unfold bankFn
  split_ifs  <;> omega

def bank : Equiv.Perm Nat := ⟨bankFn,bankFn,bank_invol,bank_invol⟩
def relocate : Equiv.Perm Wire :=
  (shifted bank).trans ((shifted (Placement5.pi 51)).trans (Equiv.swap (base 1796) (base 1285)))
def endpointMap : Equiv.Perm Wire := relocate.trans
  ⟨OB5.sig 511,OB5.sig 511,OB5.sig_invol 511 (by decide),OB5.sig_invol 511 (by decide)⟩

def centerT : Program := renameProgram endpointMap NewHalfField5.centerT
def canonT : Program := renameProgram endpointMap NewHalfField5.canonT
abbrev copyN := NewHalfField5.copyN

private def BankRegion (i : Nat) : Prop := (512 ≤ i ∧ i < 767) ∨ (1540 ≤ i ∧ i < 1795)

private theorem bank_fix (i : Nat) (h : ¬BankRegion i) : bank i=i := by
  change bankFn i=i
  simp only [BankRegion,not_or] at h
  simp [bankFn,h.1,h.2]

private theorem shifted_bank_zero (s : State) (hz : ∀i,BankRegion i → s.basis (base i)=false) :
    pullState (shifted bank) s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (shifted bank q)=s.basis q
    by_cases small : q < 16
    · change s.basis (shiftedFn bank q)=s.basis q
      simp only [shiftedFn,if_pos small]
    · have e : q=base (q-16) := by change q=q-16+16; exact (Nat.sub_add_cancel (Nat.le_of_not_gt small)).symm
      rw [e,shifted_base]
      by_cases inside : BankRegion (q-16)
      · have mapped : BankRegion (bank (q-16)) := by
          by_contra outside
          have eq := bank.injective (bank_fix _ outside)
          exact outside (eq.symm ▸ inside)
        exact (hz _ mapped).trans (hz _ inside).symm
      · rw [bank_fix _ inside]

private theorem env_bank (origin : BasisState) (env : Env base origin) (i : Nat)
    (hi : BankRegion i ∨ i=1796) : origin (base i)=false := by
  rcases hi with (h|h)|h
  · exact OffsetCleanupBorrowedCaller.maskBit_zero base origin env.1 i (by omega) (by omega)
  · have mem := DirectSkywalk.arith_mem base 1540 257 i (by omega) (by omega)
    exact (regValue_zero _ _).mp env.1 _ (by
      simp [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,mem])
  · subst i
    have mem := DirectSkywalk.arith_mem base 1540 257 1796 (by omega) (by omega)
    exact (regValue_zero _ _).mp env.1 _ (by
      simp [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,mem])

private theorem encoder_away (i : Nat) (hi : BankRegion i ∨ i=1796) :
    base i∉wires (NewHistory5.allEncode base 102) := by
  intro h
  have mem := List.mem_toFinset.mp (allEncode_history_support base 102 (by decide) h)
  simp only [List.mem_append,wireBlock,List.mem_map,List.mem_range'_1] at mem
  rcases mem with ⟨j,hj,eq⟩|⟨j,hj,eq⟩
  all_goals
    have same := base_injective eq
    unfold BankRegion at hi
    omega

private theorem frame_banks (origin : BasisState) (env : Env base origin) (s raw : State)
    (encoded : s=run (NewHistory5.allEncode base 102) [] raw)
    (keep : ∀i,BankRegion i ∨ i=1796 → raw.basis (base i)=origin (base i)) :
    (∀i,BankRegion i → s.basis (base i)=false) ∧ s.basis (base 1796)=false := by
  have z (i : Nat) (hi : BankRegion i ∨ i=1796) : s.basis (base i)=false := by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_away i hi)).trans
      ((keep i hi).trans (env_bank origin env i hi))
  exact ⟨fun i hi => z i (Or.inl hi),z 1796 (Or.inr rfl)⟩

private theorem canonical_banks (origin : BasisState) (env : Env base origin)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame5 origin X 0 s) :
    (∀i,BankRegion i → s.basis (base i)=false) ∧ s.basis (base 1796)=false := by
  obtain ⟨raw,_,f,e⟩ := frame
  apply frame_banks origin env s raw e
  intro i hi
  apply f.2.2
  · intro mem
    rw [skywalkShared_field_z] at mem
    simp only [wireBlock,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
      List.mem_map,List.mem_range'_1] at mem
    unfold BankRegion at hi
    obtain ⟨j,hj,eq⟩ := mem
    have same := base_injective eq
    omega
  · intro mem
    change base i∈wireBlock base 770 257 at mem
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp mem
    simp only [List.mem_range'_1] at hj
    have same := base_injective eq
    unfold BankRegion at hi
    omega

private theorem field_banks (origin : BasisState) (env : Env base origin)
    (X Y : Fp) (s : State) (frame : EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (∀i,BankRegion i → s.basis (base i)=false) ∧ s.basis (base 1796)=false := by
  obtain ⟨raw,_,f,e⟩ := frame
  apply frame_banks origin env s raw e
  intro i hi
  apply f.2.2
  all_goals
    intro mem
    simp only [balancedSharedPorts_r,balancedSharedPorts_y] at mem
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp mem
    simp only [List.mem_range'_1] at hj
    have same := base_injective eq
    unfold BankRegion at hi
    omega

private theorem canonical_zero (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (env : Env base origin) (legal : RawLegal base 102 origin)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (frame : EncodedCanonicalFrame5 origin X 0 s) :
    ∀q,Placement5.zeroRegion q → s.basis (base q)=false := by
  intro q hq
  have before := NewHalfField5.encodedCanonical_pool_basis5 hn origin ha X s frame
  have pool : base q∈skywalkPoolWires base := by
    apply List.mem_map.mpr
    refine ⟨q,?_,rfl⟩
    simp only [List.mem_range'_1]
    rcases hq with h|h
    · unfold Placement5.workRegion at h; omega
    · unfold Placement5.holeRegion at h; omega
  rw [before _ pool]
  rcases hq with work|hole
  · exact (run_preserves_outside _ [] ({phase:=false,basis:=origin}:State) _
      (encoder_away q (Or.inl (Or.inl (by unfold Placement5.workRegion at work; omega))))).trans
      (env_bank origin env q (Or.inl (Or.inl (by unfold Placement5.workRegion at work; omega))))
  · have recover := Placement5.hole_recover q hole
    rw [←recover.2]
    exact allEncode_holes_zero base base_pool_nodup ({phase:=false,basis:=origin}:State) [] legal
      (Placement5.holeIndex q) recover.1

private theorem relocation_eq (P : Program) (s : State) (m : List Bool)
    (b0 : ∀i,BankRegion i → s.basis (base i)=false)
    (b1 : ∀i,BankRegion i → (run P m s).basis (base i)=false)
    (z0 : ∀i,Placement5.zeroRegion i → s.basis (base i)=false)
    (z1 : ∀i,Placement5.zeroRegion i → (run P m s).basis (base i)=false)
    (f0 : s.basis (base 1796)=false) (f1 : (run P m s).basis (base 1796)=false) :
    run (renameProgram relocate P) m s=run P m s := by
  have bankRun : run (renameProgram (shifted bank) P) m s=run P m s := by
    apply pullState_perm_injective (shifted bank)
    rw [run_rename _ (shifted bank).injective,shifted_bank_zero s b0,shifted_bank_zero _ b1]
  have piRun : run (renameProgram (shifted (Placement5.pi 51))
      (renameProgram (shifted bank) P)) m s=run P m s := by
    apply pullState_perm_injective (shifted (Placement5.pi 51))
    rw [run_rename _ (shifted (Placement5.pi 51)).injective,
      Placement5.shifted_zero_boundary _ (Placement5.pi_outside 51 · (by decide)) s z0,
      bankRun,Placement5.shifted_zero_boundary _ (Placement5.pi_outside 51 · (by decide)) _ z1]
  have hole : Placement5.zeroRegion 1285 := by right; unfold Placement5.holeRegion; decide
  have swapRun := NewFieldFrameOB5.rebind_swap_run (base 1796) (base 1285)
    (renameProgram (shifted (Placement5.pi 51)) (renameProgram (shifted bank) P)) s m
    f0 (z0 _ hole) (by rw [piRun]; exact f1) (by rw [piRun]; exact z1 _ hole)
  simpa only [relocate,Equiv.trans_apply,renameProgram_comp] using swapRun.trans piRun

attribute [local irreducible] HalfField.centerT HalfField.canonT
set_option maxHeartbeats 30000

theorem logical_center_eq (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame5 origin X 0 s) :
    run (renameProgram relocate NewHalfField5.centerT) m s=run NewHalfField5.centerT m s := by
  have c := NewHalfField5.center_frame hn origin env.1 env.2.1 hr env.2.2 X s m input
  have a := canonical_banks origin env X s input
  have b := field_banks origin env _ _ _ c.2
  exact relocation_eq NewHalfField5.centerT s m a.1 b.1 (canonical_zero hn origin env legal ha X s input)
    (NewHistory5.encoded_zero_region base (base 2409) hn ho origin env legal _ _ _ c.2) a.2 b.2

theorem logical_canon_eq (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool)
    (input : EncodedFieldFrame5 base (base 2409) origin X 0 s) :
    run (renameProgram relocate NewHalfField5.canonT) m s=run NewHalfField5.canonT m s := by
  have c := NewHalfField5.canon_frame hn origin env.1 env.2.1 hr env.2.2 X s m input
  have a := field_banks origin env _ _ _ input
  have b := canonical_banks origin env _ _ c.2
  exact relocation_eq NewHalfField5.canonT s m a.1 b.1
    (NewHistory5.encoded_zero_region base (base 2409) hn ho origin env legal _ _ _ input)
    (canonical_zero hn origin env legal ha _ _ c.2) a.2 b.2

private theorem endpointMap_rename (P : Program) :
    renameProgram endpointMap P=renameProgram (OB5.sig 511) (renameProgram relocate P) := by
  change renameProgram ((OB5.sig 511) ∘ relocate) P=_
  exact (renameProgram_comp (OB5.sig 511) relocate P).symm

private theorem center_eq : centerT=renameProgram (OB5.sig 511)
    (renameProgram relocate NewHalfField5.centerT) := endpointMap_rename _

private theorem canon_eq : canonT=renameProgram (OB5.sig 511)
    (renameProgram relocate NewHalfField5.canonT) := endpointMap_rename _

private theorem placed_step (e : Wire → Wire) (he : Function.Injective e) (P : Program)
    (I O : State → Prop)
    (correct : ∀s m,I s → (run P m s).phase=s.phase ∧ O (run P m s))
    (s : State) (m : List Bool) (input : I (pullState e s)) :
    (run (renameProgram e P) m s).phase=s.phase ∧ O (pullState e (run (renameProgram e P) m s)) := by
  have c := correct (pullState e s) m input
  have same := ECDSAAdd.run_rename e he P m s
  rw [←same] at c
  exact c

attribute [local irreducible] relocate endpointMap

theorem center_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedFieldFrame origin (X/2) 0 (run centerT m s) := by
  have correct : ∀t records,EncodedCanonicalFrame5 origin X 0 t →
      (run (renameProgram relocate NewHalfField5.centerT) records t).phase=t.phase ∧
      EncodedFieldFrame5 base (base 2409) origin (X/2) 0
        (run (renameProgram relocate NewHalfField5.centerT) records t) := by
    intro t records hin
    rw [logical_center_eq hn ho origin env legal hr ha X t records hin]
    exact NewHalfField5.center_frame hn origin env.1 env.2.1 hr env.2.2 X t records hin
  have c := placed_step (OB5.sig 511) (OB5.sig_injective 511 (by decide))
    (renameProgram relocate NewHalfField5.centerT) _ _ correct s m input
  rw [←center_eq] at c
  exact c

theorem canon_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run canonT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  have correct : ∀t records,EncodedFieldFrame5 base (base 2409) origin X 0 t →
      (run (renameProgram relocate NewHalfField5.canonT) records t).phase=t.phase ∧
      EncodedCanonicalFrame5 origin (2*X) 0
        (run (renameProgram relocate NewHalfField5.canonT) records t) := by
    intro t records hin
    rw [logical_canon_eq hn ho origin env legal hr ha X t records hin]
    exact NewHalfField5.canon_frame hn origin env.1 env.2.1 hr env.2.2 X t records hin
  have c := placed_step (OB5.sig 511) (OB5.sig_injective 511 (by decide))
    (renameProgram relocate NewHalfField5.canonT) _ _ correct s m input
  rw [←canon_eq] at c
  exact c

theorem copyN_rename : renameProgram (OB5.sig 511) copyN=copyN := by
  have fixed (start len : Nat) (h : (770 ≤ start ∧ start+len ≤ 1026) ∨ (2056 ≤ start ∧ start+len ≤ 2312)) :
      (wireBlock base start len).map (OB5.sig 511)=wireBlock base start len := by
    calc
      (wireBlock base start len).map (OB5.sig 511)=(wireBlock base start len).map id := by
        apply List.map_congr_left
        intro q hq
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
        simp only [List.mem_range'_1] at hi
        rw [OB5.sig_base 511 i (by decide)]
        have outside : ¬((1285 ≤ i ∧ i ≤ 1028+511) ∨ (2053 ≤ i+511 ∧ i ≤ 1796)) := by omega
        simp only [if_neg outside,id_eq]
      _=wireBlock base start len := List.map_id _

  simp only [copyN,NewHalfField5.copyN,HalfField.copyN,FieldRename.copyRegister_natural,
    Option.map_none,HalfField.ports,balancedSharedPorts_r,balancedSharedPorts_y,
    fixed 2056 256 (Or.inr ⟨by omega,by omega⟩),fixed 770 256 (Or.inl ⟨by omega,by omega⟩)]

theorem copy_fill (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run copyN m s).phase=s.phase ∧ NewFieldFrameOB5.EncodedFieldFrame origin X X (run copyN m s) := by
  have c := NewFieldFrameOB5.placed_step copyN origin X 0 X X
    (fun t records h => NewHalfField5.copy_fill hn origin X t records h) s m input
  rw [copyN_rename] at c
  exact c

theorem copy_clear (hn : (skywalkSharedWires base).Nodup) (origin : BasisState)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X X s) :
    (run copyN m s).phase=s.phase ∧ NewFieldFrameOB5.EncodedFieldFrame origin X 0 (run copyN m s) := by
  have c := NewFieldFrameOB5.placed_step copyN origin X X X 0
    (fun t records h => NewHalfField5.copy_clear hn origin X t records h) s m input
  rw [copyN_rename] at c
  exact c

attribute [local irreducible] toffoliCount measurementCount

theorem endpoint_counts : toffoliCount centerT=254 ∧ measurementCount centerT=254 ∧
    toffoliCount canonT=254 ∧ measurementCount canonT=254 := by
  have old : toffoliCount NewHalfField5.centerT=254 ∧ measurementCount NewHalfField5.centerT=254 ∧
      toffoliCount NewHalfField5.canonT=254 ∧ measurementCount NewHalfField5.canonT=254 := by
    simpa only [NewHalfField5.centerT,NewHalfField5.canonT,HalfField.centerT,HalfField.canonT] using
      HalfConvert.counts HalfField.tgt (balancedSharedTargetConvert_widths base)
  have a := renameProgram_counts endpointMap NewHalfField5.centerT
  have b := renameProgram_counts endpointMap NewHalfField5.canonT
  exact ⟨a.1.trans old.1,a.2.trans old.2.1,b.1.trans old.2.2.1,b.2.trans old.2.2.2⟩

theorem endpoint_physical (hn : (skywalkSharedWires base).Nodup) :
    GatePhysical centerT ∧ GatePhysical canonT ∧ GatePhysical copyN := by
  have old := HalfConvert.physical HalfField.tgt (balancedSharedTargetConvert_widths base)
    (balancedSharedTargetConvert_nodup base hn)
  have oldCenter : GatePhysical NewHalfField5.centerT := by
    simpa only [NewHalfField5.centerT,HalfField.centerT] using old.1
  have oldCanon : GatePhysical NewHalfField5.canonT := by
    simpa only [NewHalfField5.canonT,HalfField.canonT] using old.2
  exact ⟨gatePhysical_rename endpointMap endpointMap.injective _ oldCenter,
    gatePhysical_rename endpointMap endpointMap.injective _ oldCanon,
    copyRegister_physical none _ _ (balancedSharedLayout_pairND base (base 2409) hn) (by simp)⟩

theorem endpoint_gateSlots_le : Challenge.gateSlots centerT ≤ 6000 ∧
    Challenge.gateSlots canonT ≤ 6000 ∧ Challenge.gateSlots copyN ≤ 256 := by
  have a : Challenge.gateSlots NewHalfField5.centerT ≤ 6000 ∧ Challenge.gateSlots NewHalfField5.canonT ≤ 6000 :=
    HalfLane.convert_gateSlots_le
  have cp : Challenge.gateSlots copyN ≤ 256 := by
    simp only [copyN,NewHalfField5.copyN,HalfField.copyN,HalfField.ports,
      Baselines.copyRegister_gateSlots,balancedSharedPorts_r,wireBlock_length]
    omega
  exact ⟨by simpa only [centerT,Baselines.rename_gateSlots] using a.1,
    by simpa only [canonT,Baselines.rename_gateSlots] using a.2,cp⟩

end ECDSAAdd.Entrant.NewHalfFieldOB5

namespace ECDSAAdd.Entrant.NewOwnPlusEndpoint
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
open OwnPlusHost
attribute [local irreducible] run wires

theorem encoder_free (q : Nat) (hq : q=766 ∨ q=768) :
    base q∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have mem:=NewHistory5.allEncode_history_support base 102 (by omega) used
  simp only [List.mem_toFinset,List.mem_append] at mem
  rcases mem with lo|hi
  · exact not_block q 0 512 (by omega) lo
  · exact not_block q 1028 512 (by omega) hi

theorem canonical_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=766 ∨ q=768) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have z:base q∉(skywalkSharedField base).z:=by
    rw [skywalkShared_field_z]
    exact not_block q 2056 257 (by omega)
  have a:base q∉(skywalkSharedField base).a:=not_block q 770 257 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ z a)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem field_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=766 ∨ q=768) (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have r:base q∉(balancedSharedPorts base (base 2409)).r:=by
    rw [balancedSharedPorts_r]
    exact not_block q 2056 256 (by omega)
  have y:base q∉(balancedSharedPorts base (base 2409)).y:=by
    rw [balancedSharedPorts_y]
    exact not_block q 770 256 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ r y)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem env_zero (origin : BasisState) (env : Env base origin)
    (hr : origin (base 2312)=false) (q : Nat) (hq : q=766 ∨ q=768) : origin (base q)=false := by
  apply OneBankCell5.clean_of_env_work base (base 2409) origin env hr
  rw [OneBankCell5.ports_work]
  rcases hq with rfl|rfl <;> simp [OneBankCell5.workIds]

def swap : Equiv.Perm Wire:=Equiv.swap (base 766) (base 768)
def centerT : Program:=renameProgram swap NewHalfFieldOB5.centerT
def canonT : Program:=renameProgram swap NewHalfFieldOB5.canonT

theorem center_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedFieldFrame origin (X/2) 0 (run centerT m s) := by
  have old:=NewHalfFieldOB5.center_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=766 ∨ q=768) : s.basis (base q)=false :=
    (canonical_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=766 ∨ q=768) : (run NewHalfFieldOB5.centerT m s).basis (base q)=false :=
    (field_at origin (X/2) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 766) (base 768) NewHalfFieldOB5.centerT s m
    (before 766 (Or.inl rfl)) (before 768 (Or.inr rfl))
    (after 766 (Or.inl rfl)) (after 768 (Or.inr rfl))
  simpa only [centerT,swap,eq] using old

theorem canon_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run canonT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  have old:=NewHalfFieldOB5.canon_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=766 ∨ q=768) : s.basis (base q)=false :=
    (field_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=766 ∨ q=768) : (run NewHalfFieldOB5.canonT m s).basis (base q)=false :=
    (canonical_at origin (2*X) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 766) (base 768) NewHalfFieldOB5.canonT s m
    (before 766 (Or.inl rfl)) (before 768 (Or.inr rfl))
    (after 766 (Or.inl rfl)) (after 768 (Or.inr rfl))
  simpa only [canonT,swap,eq] using old
theorem endpoint_counts : toffoliCount centerT=254 ∧ measurementCount centerT=254 ∧
    toffoliCount canonT=254 ∧ measurementCount canonT=254 := by
  simpa only [centerT,canonT,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
    using NewHalfFieldOB5.endpoint_counts

theorem endpoint_physical (hn : (skywalkSharedWires base).Nodup) :
    GatePhysical centerT ∧ GatePhysical canonT ∧ GatePhysical NewHalfFieldOB5.copyN := by
  have old:=NewHalfFieldOB5.endpoint_physical hn
  exact ⟨gatePhysical_rename swap swap.injective _ old.1,
    gatePhysical_rename swap swap.injective _ old.2.1,old.2.2⟩

theorem endpoint_gateSlots_le : Challenge.gateSlots centerT≤6000 ∧ Challenge.gateSlots canonT≤6000 ∧
    Challenge.gateSlots NewHalfFieldOB5.copyN≤256 := by
  simpa only [centerT,canonT,Baselines.rename_gateSlots] using NewHalfFieldOB5.endpoint_gateSlots_le

theorem old_unused (q : Nat) (hq : q=768 ∨ q=2312) :
    base q∉wires NewHalfFieldOB5.centerT ∧ base q∉wires NewHalfFieldOB5.canonT := by
  have no : base q∉(HalfField.ids.map base).toFinset := by
    intro h
    obtain ⟨i,hi,e⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
    have eq:=base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
    omega
  have a:base q∉wires NewHalfField5.centerT:=fun h=>no (@HalfField.centerT_sites (base q) h)
  have b:base q∉wires NewHalfField5.canonT:=fun h=>no (@HalfField.canonT_sites (base q) h)
  have fix : NewHalfFieldOB5.endpointMap (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  exact ⟨rename_avoid _ _ _ fix a,rename_avoid _ _ _ fix b⟩

theorem plus_free : base 766∉wires centerT ∧ base 766∉wires canonT := by
  have avoid (P : Program) (hp : base 768∉wires P) : base 766∉wires (renameProgram swap P) := by
    rw [renameProgram_support]
    intro used
    obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
    have back:swap (base 768)=base 766:=Equiv.swap_apply_right _ _
    have same:old=base 768:=swap.injective (e.trans back.symm)
    exact hp (same ▸ used)
  exact ⟨avoid _ (old_unused 768 (Or.inl rfl)).1,avoid _ (old_unused 768 (Or.inl rfl)).2⟩

theorem parity_free : base 2312∉wires centerT ∧ base 2312∉wires canonT := by
  have fix:swap (base 2312)=base 2312:=by decide +kernel
  exact ⟨rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).1,
    rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).2⟩

end ECDSAAdd.Entrant.NewOwnPlusEndpoint

namespace ECDSAAdd.Entrant.NewOwnGuardEndpoint
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
open OwnPlusHost
attribute [local irreducible] run wires

theorem encoder_free (q : Nat) (hq : q=765 ∨ q=767) :
    base q∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have mem:=NewHistory5.allEncode_history_support base 102 (by omega) used
  simp only [List.mem_toFinset,List.mem_append] at mem
  rcases mem with lo|hi
  · exact not_block q 0 512 (by omega) lo
  · exact not_block q 1028 512 (by omega) hi

theorem canonical_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=765 ∨ q=767) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have z:base q∉(skywalkSharedField base).z:=by
    rw [skywalkShared_field_z]
    exact not_block q 2056 257 (by omega)
  have a:base q∉(skywalkSharedField base).a:=not_block q 770 257 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ z a)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem field_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=765 ∨ q=767) (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have r:base q∉(balancedSharedPorts base (base 2409)).r:=by
    rw [balancedSharedPorts_r]
    exact not_block q 2056 256 (by omega)
  have y:base q∉(balancedSharedPorts base (base 2409)).y:=by
    rw [balancedSharedPorts_y]
    exact not_block q 770 256 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ r y)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem env_zero (origin : BasisState) (env : Env base origin)
    (hr : origin (base 2312)=false) (q : Nat) (hq : q=765 ∨ q=767) : origin (base q)=false := by
  apply OneBankCell5.clean_of_env_work base (base 2409) origin env hr
  rw [OneBankCell5.ports_work]
  rcases hq with rfl|rfl <;> simp [OneBankCell5.workIds]

def swap : Equiv.Perm Wire:=Equiv.swap (base 765) (base 767)
def centerT : Program:=renameProgram swap NewOwnPlusEndpoint.centerT
def canonT : Program:=renameProgram swap NewOwnPlusEndpoint.canonT

theorem center_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedFieldFrame origin (X/2) 0 (run centerT m s) := by
  have old:=NewOwnPlusEndpoint.center_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=765 ∨ q=767) : s.basis (base q)=false :=
    (canonical_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=765 ∨ q=767) : (run NewOwnPlusEndpoint.centerT m s).basis (base q)=false :=
    (field_at origin (X/2) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 765) (base 767) NewOwnPlusEndpoint.centerT s m
    (before 765 (Or.inl rfl)) (before 767 (Or.inr rfl))
    (after 765 (Or.inl rfl)) (after 767 (Or.inr rfl))
  simpa only [centerT,swap,eq] using old

theorem canon_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run canonT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  have old:=NewOwnPlusEndpoint.canon_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=765 ∨ q=767) : s.basis (base q)=false :=
    (field_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=765 ∨ q=767) : (run NewOwnPlusEndpoint.canonT m s).basis (base q)=false :=
    (canonical_at origin (2*X) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 765) (base 767) NewOwnPlusEndpoint.canonT s m
    (before 765 (Or.inl rfl)) (before 767 (Or.inr rfl))
    (after 765 (Or.inl rfl)) (after 767 (Or.inr rfl))
  simpa only [canonT,swap,eq] using old
theorem endpoint_counts : toffoliCount centerT=254 ∧ measurementCount centerT=254 ∧
    toffoliCount canonT=254 ∧ measurementCount canonT=254 := by
  simpa only [centerT,canonT,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
    using NewOwnPlusEndpoint.endpoint_counts

theorem endpoint_physical (hn : (skywalkSharedWires base).Nodup) :
    GatePhysical centerT ∧ GatePhysical canonT ∧ GatePhysical NewHalfFieldOB5.copyN := by
  have old:=NewOwnPlusEndpoint.endpoint_physical hn
  exact ⟨gatePhysical_rename swap swap.injective _ old.1,
    gatePhysical_rename swap swap.injective _ old.2.1,old.2.2⟩

theorem endpoint_gateSlots_le : Challenge.gateSlots centerT≤6000 ∧ Challenge.gateSlots canonT≤6000 ∧
    Challenge.gateSlots NewHalfFieldOB5.copyN≤256 := by
  simpa only [centerT,canonT,Baselines.rename_gateSlots] using NewOwnPlusEndpoint.endpoint_gateSlots_le

theorem old_unused (q : Nat) (hq : q=767 ∨ q=2312) :
    base q∉wires NewOwnPlusEndpoint.centerT ∧ base q∉wires NewOwnPlusEndpoint.canonT := by
  have no : base q∉(HalfField.ids.map base).toFinset := by
    intro h
    obtain ⟨i,hi,e⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
    have eq:=base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
    omega
  have a:base q∉wires NewHalfField5.centerT:=fun h=>no (@HalfField.centerT_sites (base q) h)
  have b:base q∉wires NewHalfField5.canonT:=fun h=>no (@HalfField.canonT_sites (base q) h)
  have fix : NewHalfFieldOB5.endpointMap (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  have first : base q∉wires NewHalfFieldOB5.centerT ∧ base q∉wires NewHalfFieldOB5.canonT :=
    ⟨OwnPlusHost.rename_avoid _ _ _ fix a,OwnPlusHost.rename_avoid _ _ _ fix b⟩
  have fixPlus : NewOwnPlusEndpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fixPlus first.1,OwnPlusHost.rename_avoid _ _ _ fixPlus first.2⟩

theorem plus_free : base 765∉wires centerT ∧ base 765∉wires canonT := by
  have avoid (P : Program) (hp : base 767∉wires P) : base 765∉wires (renameProgram swap P) := by
    rw [renameProgram_support]
    intro used
    obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
    have back:swap (base 767)=base 765:=Equiv.swap_apply_right _ _
    have same:old=base 767:=swap.injective (e.trans back.symm)
    exact hp (same ▸ used)
  exact ⟨avoid _ (old_unused 767 (Or.inl rfl)).1,avoid _ (old_unused 767 (Or.inl rfl)).2⟩

theorem parity_free : base 2312∉wires centerT ∧ base 2312∉wires canonT := by
  have fix:swap (base 2312)=base 2312:=by decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).1,
    OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).2⟩

end ECDSAAdd.Entrant.NewOwnGuardEndpoint

namespace ECDSAAdd.Entrant.NewOwnQ4Endpoint
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
open OwnPlusHost
attribute [local irreducible] run wires

theorem encoder_free (q : Nat) (hq : q=767 ∨ q=1026) :
    base q∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have mem:=NewHistory5.allEncode_history_support base 102 (by omega) used
  simp only [List.mem_toFinset,List.mem_append] at mem
  rcases mem with lo|hi
  · exact not_block q 0 512 (by omega) lo
  · exact not_block q 1028 512 (by omega) hi

theorem canonical_at (origin : BasisState) (env : Env base origin) (X : Fp) (s : State) (q : Nat)
    (hq : q=767 ∨ q=1026) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    s.basis (base q)=origin (base q) := by
  rcases hq with rfl|rfl
  · exact NewOwnGuardEndpoint.canonical_at origin X 0 s 767 (Or.inr rfl) input
  · obtain ⟨raw,_,pair,encoded⟩:=input
    have member : base 1026∈(skywalkSharedField base).a := by
      simp only [skywalkSharedField,wireBlock,List.mem_map,List.mem_range'_1]
      exact ⟨1026,by omega,rfl⟩
    have value : regValue (skywalkSharedField base).a raw.basis=0 := by simpa using pair.2.1
    have rawzero : raw.basis (base 1026)=false := (regValue_zero _ _).mp value _ member
    have encodedzero : (pullState (OB5.sig 511) s).basis (base 1026)=false := by
      rw [encoded]
      exact (run_preserves_outside _ [] raw _ (encoder_free 1026 (Or.inr rfl))).trans rawzero
    have fix : OB5.sig 511 (base 1026)=base 1026 := by decide +kernel
    have zero : s.basis (base 1026)=false := by simpa only [pullState,fix] using encodedzero
    exact zero.trans env.2.2.symm

theorem field_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=767 ∨ q=1026) (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have r:base q∉(balancedSharedPorts base (base 2409)).r:=by
    rw [balancedSharedPorts_r]
    exact not_block q 2056 256 (by omega)
  have y:base q∉(balancedSharedPorts base (base 2409)).y:=by
    rw [balancedSharedPorts_y]
    exact not_block q 770 256 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ r y)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem env_zero (origin : BasisState) (env : Env base origin)
    (hr : origin (base 2312)=false) (q : Nat) (hq : q=767 ∨ q=1026) : origin (base q)=false := by
  rcases hq with rfl|rfl
  · exact NewOwnGuardEndpoint.env_zero origin env hr 767 (Or.inr rfl)
  · exact env.2.2

def swap : Equiv.Perm Wire:=Equiv.swap (base 767) (base 1026)
def centerT : Program:=renameProgram swap NewOwnGuardEndpoint.centerT
def canonT : Program:=renameProgram swap NewOwnGuardEndpoint.canonT

theorem center_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedFieldFrame origin (X/2) 0 (run centerT m s) := by
  have old:=NewOwnGuardEndpoint.center_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=767 ∨ q=1026) : s.basis (base q)=false :=
    (canonical_at origin env X s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=767 ∨ q=1026) : (run NewOwnGuardEndpoint.centerT m s).basis (base q)=false :=
    (field_at origin (X/2) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 767) (base 1026) NewOwnGuardEndpoint.centerT s m
    (before 767 (Or.inl rfl)) (before 1026 (Or.inr rfl))
    (after 767 (Or.inl rfl)) (after 1026 (Or.inr rfl))
  simpa only [centerT,swap,eq] using old

theorem canon_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run canonT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  have old:=NewOwnGuardEndpoint.canon_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=767 ∨ q=1026) : s.basis (base q)=false :=
    (field_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=767 ∨ q=1026) : (run NewOwnGuardEndpoint.canonT m s).basis (base q)=false :=
    (canonical_at origin env (2*X) _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 767) (base 1026) NewOwnGuardEndpoint.canonT s m
    (before 767 (Or.inl rfl)) (before 1026 (Or.inr rfl))
    (after 767 (Or.inl rfl)) (after 1026 (Or.inr rfl))
  simpa only [canonT,swap,eq] using old
theorem endpoint_counts : toffoliCount centerT=254 ∧ measurementCount centerT=254 ∧
    toffoliCount canonT=254 ∧ measurementCount canonT=254 := by
  simpa only [centerT,canonT,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
    using NewOwnGuardEndpoint.endpoint_counts

theorem endpoint_physical (hn : (skywalkSharedWires base).Nodup) :
    GatePhysical centerT ∧ GatePhysical canonT ∧ GatePhysical NewHalfFieldOB5.copyN := by
  have old:=NewOwnGuardEndpoint.endpoint_physical hn
  exact ⟨gatePhysical_rename swap swap.injective _ old.1,
    gatePhysical_rename swap swap.injective _ old.2.1,old.2.2⟩

theorem endpoint_gateSlots_le : Challenge.gateSlots centerT≤6000 ∧ Challenge.gateSlots canonT≤6000 ∧
    Challenge.gateSlots NewHalfFieldOB5.copyN≤256 := by
  simpa only [centerT,canonT,Baselines.rename_gateSlots] using NewOwnGuardEndpoint.endpoint_gateSlots_le

theorem old_unused (q : Nat) (hq : q=1026 ∨ q=2312) :
    base q∉wires NewOwnGuardEndpoint.centerT ∧ base q∉wires NewOwnGuardEndpoint.canonT := by
  have no : base q∉(HalfField.ids.map base).toFinset := by
    intro h
    obtain ⟨i,hi,e⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
    have eq:=base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
    omega
  have a:base q∉wires NewHalfField5.centerT:=fun h=>no (@HalfField.centerT_sites (base q) h)
  have b:base q∉wires NewHalfField5.canonT:=fun h=>no (@HalfField.canonT_sites (base q) h)
  have fix : NewHalfFieldOB5.endpointMap (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  have first : base q∉wires NewHalfFieldOB5.centerT ∧ base q∉wires NewHalfFieldOB5.canonT :=
    ⟨OwnPlusHost.rename_avoid _ _ _ fix a,OwnPlusHost.rename_avoid _ _ _ fix b⟩
  have fixPlus : NewOwnPlusEndpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  have second : base q∉wires NewOwnPlusEndpoint.centerT ∧ base q∉wires NewOwnPlusEndpoint.canonT :=
    ⟨OwnPlusHost.rename_avoid _ _ _ fixPlus first.1,OwnPlusHost.rename_avoid _ _ _ fixPlus first.2⟩
  have fixGuard : NewOwnGuardEndpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fixGuard second.1,OwnPlusHost.rename_avoid _ _ _ fixGuard second.2⟩

theorem plus_free : base 767∉wires centerT ∧ base 767∉wires canonT := by
  have avoid (P : Program) (hp : base 1026∉wires P) : base 767∉wires (renameProgram swap P) := by
    rw [renameProgram_support]
    intro used
    obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
    have back:swap (base 1026)=base 767:=Equiv.swap_apply_right _ _
    have same:old=base 1026:=swap.injective (e.trans back.symm)
    exact hp (same ▸ used)
  exact ⟨avoid _ (old_unused 1026 (Or.inl rfl)).1,avoid _ (old_unused 1026 (Or.inl rfl)).2⟩

theorem parity_free : base 2312∉wires centerT ∧ base 2312∉wires canonT := by
  have fix:swap (base 2312)=base 2312:=by decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).1,
    OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).2⟩

end ECDSAAdd.Entrant.NewOwnQ4Endpoint

namespace ECDSAAdd.Entrant.NewOwnQ5Endpoint
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
open OwnPlusHost
attribute [local irreducible] run wires

theorem encoder_free (q : Nat) (hq : q=1026 ∨ q=1540) :
    base q∉wires (NewHistory5.allEncode base 102) := by
  intro used
  have mem:=NewHistory5.allEncode_history_support base 102 (by omega) used
  simp only [List.mem_toFinset,List.mem_append] at mem
  rcases mem with lo|hi
  · exact not_block q 0 512 (by omega) lo
  · exact not_block q 1028 512 (by omega) hi

theorem canonical_at (origin : BasisState) (env : Env base origin) (X : Fp) (s : State) (q : Nat)
    (hq : q=1026 ∨ q=1540) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    s.basis (base q)=origin (base q) := by
  rcases hq with rfl|rfl
  · exact NewOwnQ4Endpoint.canonical_at origin env X s 1026 (Or.inr rfl) input
  · obtain ⟨raw,_,pair,encoded⟩:=input
    have z:base 1540∉(skywalkSharedField base).z:=by
      rw [skywalkShared_field_z];exact not_block 1540 2056 257 (by omega)
    have a:base 1540∉(skywalkSharedField base).a:=not_block 1540 770 257 (by omega)
    have eq:(pullState (OB5.sig 511) s).basis (base 1540)=origin (base 1540):=by
      rw [encoded]
      exact (run_preserves_outside _ [] raw _ (encoder_free 1540 (Or.inr rfl))).trans (pair.2.2 _ z a)
    have fix:OB5.sig 511 (base 1540)=base 1540:=by decide +kernel
    simpa only [pullState,fix] using eq

theorem field_at (origin : BasisState) (X Y : Fp) (s : State) (q : Nat)
    (hq : q=1026 ∨ q=1540) (input : NewFieldFrameOB5.EncodedFieldFrame origin X Y s) :
    s.basis (base q)=origin (base q) := by
  obtain ⟨raw,_,pair,encoded⟩:=input
  have r:base q∉(balancedSharedPorts base (base 2409)).r:=by
    rw [balancedSharedPorts_r]
    exact not_block q 2056 256 (by omega)
  have y:base q∉(balancedSharedPorts base (base 2409)).y:=by
    rw [balancedSharedPorts_y]
    exact not_block q 770 256 (by omega)
  have eq:(pullState (OB5.sig 511) s).basis (base q)=origin (base q):=by
    rw [encoded]
    exact (run_preserves_outside _ [] raw _ (encoder_free q hq)).trans (pair.2.2 _ r y)
  have fix:OB5.sig 511 (base q)=base q:=by rcases hq with rfl|rfl <;> decide +kernel
  simpa only [pullState,fix] using eq

theorem env_zero (origin : BasisState) (env : Env base origin)
    (hr : origin (base 2312)=false) (q : Nat) (hq : q=1026 ∨ q=1540) : origin (base q)=false := by
  rcases hq with rfl|rfl
  · exact env.2.2
  · apply OneBankCell5.clean_of_env_work base (base 2409) origin env hr
    rw [OneBankCell5.ports_work]
    simp [OneBankCell5.workIds]

def swap : Equiv.Perm Wire:=Equiv.swap (base 1026) (base 1540)
def centerT : Program:=renameProgram swap NewOwnQ4Endpoint.centerT
def canonT : Program:=renameProgram swap NewOwnQ4Endpoint.canonT

theorem center_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedCanonicalFrame origin X 0 s) :
    (run centerT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedFieldFrame origin (X/2) 0 (run centerT m s) := by
  have old:=NewOwnQ4Endpoint.center_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=1026 ∨ q=1540) : s.basis (base q)=false :=
    (canonical_at origin env X s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=1026 ∨ q=1540) : (run NewOwnQ4Endpoint.centerT m s).basis (base q)=false :=
    (field_at origin (X/2) 0 _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 1026) (base 1540) NewOwnQ4Endpoint.centerT s m
    (before 1026 (Or.inl rfl)) (before 1540 (Or.inr rfl))
    (after 1026 (Or.inl rfl)) (after 1540 (Or.inr rfl))
  simpa only [centerT,swap,eq] using old

theorem canon_frame (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2409∉skywalkPoolWires base) (origin : BasisState)
    (env : Env base origin) (legal : NewHistory5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (X : Fp) (s : State) (m : List Bool) (input : NewFieldFrameOB5.EncodedFieldFrame origin X 0 s) :
    (run canonT m s).phase=s.phase ∧
    NewFieldFrameOB5.EncodedCanonicalFrame origin (2*X) 0 (run canonT m s) := by
  have old:=NewOwnQ4Endpoint.canon_frame hn ho origin env legal hr ha X s m input
  have before (q : Nat) (hq : q=1026 ∨ q=1540) : s.basis (base q)=false :=
    (field_at origin X 0 s q hq input).trans (env_zero origin env hr q hq)
  have after (q : Nat) (hq : q=1026 ∨ q=1540) : (run NewOwnQ4Endpoint.canonT m s).basis (base q)=false :=
    (canonical_at origin env (2*X) _ q hq old.2).trans (env_zero origin env hr q hq)
  have eq:=NewFieldFrameOB5.rebind_swap_run (base 1026) (base 1540) NewOwnQ4Endpoint.canonT s m
    (before 1026 (Or.inl rfl)) (before 1540 (Or.inr rfl))
    (after 1026 (Or.inl rfl)) (after 1540 (Or.inr rfl))
  simpa only [canonT,swap,eq] using old
theorem endpoint_counts : toffoliCount centerT=254 ∧ measurementCount centerT=254 ∧
    toffoliCount canonT=254 ∧ measurementCount canonT=254 := by
  simpa only [centerT,canonT,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
    using NewOwnQ4Endpoint.endpoint_counts

theorem endpoint_physical (hn : (skywalkSharedWires base).Nodup) :
    GatePhysical centerT ∧ GatePhysical canonT ∧ GatePhysical NewHalfFieldOB5.copyN := by
  have old:=NewOwnQ4Endpoint.endpoint_physical hn
  exact ⟨gatePhysical_rename swap swap.injective _ old.1,
    gatePhysical_rename swap swap.injective _ old.2.1,old.2.2⟩

theorem endpoint_gateSlots_le : Challenge.gateSlots centerT≤6000 ∧ Challenge.gateSlots canonT≤6000 ∧
    Challenge.gateSlots NewHalfFieldOB5.copyN≤256 := by
  simpa only [centerT,canonT,Baselines.rename_gateSlots] using NewOwnQ4Endpoint.endpoint_gateSlots_le

theorem old_unused (q : Nat) (hq : q=1540 ∨ q=2312) :
    base q∉wires NewOwnQ4Endpoint.centerT ∧ base q∉wires NewOwnQ4Endpoint.canonT := by
  let i : Nat:=if q=1540 then 512 else 2312
  have back : NewHalfFieldOB5.endpointMap (base i)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  have no : base i∉(HalfField.ids.map base).toFinset := by
    intro h
    obtain ⟨j,hj,e⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
    have eq:=base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
    rcases hq with rfl|rfl <;> simp only [i,if_pos rfl,if_neg (by decide : (2312:Nat)≠1540)] at eq <;> omega
  have lift (P : Program) (hP : wires P⊆(HalfField.ids.map base).toFinset) :
      base q∉wires (renameProgram NewHalfFieldOB5.endpointMap P) := by
    rw [renameProgram_support]
    intro used
    obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
    have same:old=base i:=NewHalfFieldOB5.endpointMap.injective (e.trans back.symm)
    exact no (same ▸ hP used)
  have first : base q∉wires NewHalfFieldOB5.centerT ∧ base q∉wires NewHalfFieldOB5.canonT :=
    ⟨lift _ HalfField.centerT_sites,lift _ HalfField.canonT_sites⟩
  have fixPlus : NewOwnPlusEndpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  have second : base q∉wires NewOwnPlusEndpoint.centerT ∧ base q∉wires NewOwnPlusEndpoint.canonT :=
    ⟨OwnPlusHost.rename_avoid _ _ _ fixPlus first.1,OwnPlusHost.rename_avoid _ _ _ fixPlus first.2⟩
  have fixGuard : NewOwnGuardEndpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  have third : base q∉wires NewOwnGuardEndpoint.centerT ∧ base q∉wires NewOwnGuardEndpoint.canonT :=
    ⟨OwnPlusHost.rename_avoid _ _ _ fixGuard second.1,OwnPlusHost.rename_avoid _ _ _ fixGuard second.2⟩
  have fixQ4 : NewOwnQ4Endpoint.swap (base q)=base q := by
    rcases hq with rfl|rfl <;> decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fixQ4 third.1,OwnPlusHost.rename_avoid _ _ _ fixQ4 third.2⟩

theorem plus_free : base 1026∉wires centerT ∧ base 1026∉wires canonT := by
  have avoid (P : Program) (hp : base 1540∉wires P) : base 1026∉wires (renameProgram swap P) := by
    rw [renameProgram_support]
    intro used
    obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
    have back:swap (base 1540)=base 1026:=Equiv.swap_apply_right _ _
    have same:old=base 1540:=swap.injective (e.trans back.symm)
    exact hp (same ▸ used)
  exact ⟨avoid _ (old_unused 1540 (Or.inl rfl)).1,avoid _ (old_unused 1540 (Or.inl rfl)).2⟩

theorem parity_free : base 2312∉wires centerT ∧ base 2312∉wires canonT := by
  have fix:swap (base 2312)=base 2312:=by decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).1,
    OwnPlusHost.rename_avoid _ _ _ fix (old_unused 2312 (Or.inr rfl)).2⟩


end ECDSAAdd.Entrant.NewOwnQ5Endpoint
