import ECDSAAdd.Submission.Entrant.FrontierEntry1591Replay

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierSW1591
open ECDSAAdd.Arithmetic MappedCompressed CompressedFieldSupport Secp256k1 DirectSkywalk SW
attribute [local irreducible] wires

/-! ### Definitions -/

def swapBody : Program :=
  swapRegisters (base 2409) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y

def cellS (divide : Bool) (g sw : Wire) : Program :=
 if divide then selW g (base 2409) (Q6EndpointCell.half true base (base 2409))++
   selW sw (base 2409) swapBody
 else selW sw (base 2409) swapBody++
   selW g (base 2409) (Q6EndpointCell.half false base (base 2409))

def rawReplayS (divide : Bool) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => if divide then cellS true l.1.1 l.1.2++rawReplayS true ls
    else rawReplayS false ls++cellS false l.1.1 l.1.2

def basePacketS (divide : Bool) (j : Nat) : Program :=
  NewHistory5.decode base (5*j)++rawReplayS divide (Replay5.letters j)++NewHistory5.encode base (5*j)

def packetS (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacketS divide j)

def groupsS (divide : Bool) (j n : Nat) : Program :=
  PacketSequence.program divide (packetS divide) j n

def firstSwapS : Program := selW (base 1028) (base 2409) swapBody

def swapBodyM : Program :=
  UncompSwap.mswap (base 2409) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y

def firstSwapMS : Program := selW (base 1028) (base 2409) swapBodyM

def firstBodyS (divide : Bool) : Program :=
  if divide then firstSwapS++rawReplayS true Replay5.restLetters
  else rawReplayS false Replay5.restLetters++firstSwapMS

def baseFirstPacketS (divide : Bool) : Program :=
  NewHistory5.decode base 0++firstBodyS divide++NewHistory5.encode base 0

def firstPacketS (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (baseFirstPacketS divide)

def rawEndS (divide : Bool) : Program :=
  selW (base 510) (base 2409) (Q6EndpointCell.halfE divide base (base 2409))

def endPacketS (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEndS divide)

def logicalReplayS (divide : Bool) : Program :=
  if divide then firstPacketS true++groupsS true 1 101++endPacketS true
  else endPacketS false++groupsS false 1 101++firstPacketS false

def replayS (divide : Bool) : Program := renameProgram (OB5.sig 511) (logicalReplayS divide)

def segmentS (divide : Bool) : Program :=
  if divide then OwnQ5Endpoint.centerT++(replayS true++(HalfFieldOB5.copyN++OwnQ5Endpoint.canonT))
  else OwnQ5Endpoint.centerT++(HalfFieldOB5.copyN++(replayS false++OwnQ5Endpoint.canonT))

/-- The selector-hosted segment (`KernelOB5.segH`) around the selector-free segment. -/
def segHS (divide : Bool) : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap (segmentS divide) ++ [.X (base 511)])


/-! ### Frames -/

theorem Sel.castb {b b' : Wire} {k : Nat} {P' P : Program} (h : Sel b k P' P) (e : b=b') :
    Sel b' k P' P := e ▸ h

theorem selNotZero5 : ¬Placement5.zeroRegion 2400 := by
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion; omega

theorem selShift_fix (j : Nat) (hj : j < 102) : shifted (Placement5.pi j) (base 2400)=base 2400 := by
  rw [shifted_base,Placement5.pi_outside j 2400 hj selNotZero5]

theorem selShift0_fix : shifted Placement5.pi0 (base 2400)=base 2400 := by
  rw [shifted_base,Placement5.pi0_outside 2400 selNotZero5]

theorem selSig_2400 : OB5.sig 511 (base 2400)=base 2400 := by
  rw [OB5.sig_base 511 2400 (le_refl _),if_neg (by omega)]

theorem selEndpoint_fix : HalfFieldOB5.endpointMap (base 2400)=base 2400 := by
  have hb : HalfFieldOB5.bank 2400=2400 := by decide
  have hp : Placement5.pi 51 2400=2400 := Placement5.pi_outside 51 2400 (by omega) selNotZero5
  have h1 : base 2400≠base 1796 := by decide
  have h2 : base 2400≠base 1285 := by decide
  show OB5.sig 511 ((Equiv.swap (base 1796) (base 1285))
    ((shifted (Placement5.pi 51)) ((shifted HalfFieldOB5.bank) (base 2400))))=base 2400
  rw [shifted_base,hb,shifted_base,hp,Equiv.swap_apply_of_ne_of_ne h1 h2,selSig_2400]

theorem selHost_fix : HostOB5.hostSwap (base 2400)=base 2400 := by
  have a1 : base 2400≠base 2409 := by decide
  have a2 : base 2400≠base 511 := by decide
  have a3 : base 2400≠base 2410 := by decide
  have a4 : base 2400≠base 1542 := by decide
  unfold HostOB5.hostSwap
  rw [if_neg a1,if_neg a2,if_neg a3,if_neg a4]

/-! ### Label 2400 is never used outside the windows -/

theorem selX511_away : base 2400∉wires [Instr.X (base 511)] := by
  intro h
  have e : base 2400=base 511 := by simpa [wires,Instr.wires] using h
  have := base_injective e
  omega

def selW0 : Finset Wire := (base 2409::Q6EndpointCell.ids.map base).toFinset ∪ {base 2410}

theorem selW0_away : base 2400∉selW0 := by
  intro h
  simp only [selW0,Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_map,
    Finset.mem_singleton] at h
  rcases h with (e|⟨j,hj,e⟩)|e
  · have := base_injective e; omega
  · have := base_injective e; have := Q6EndpointCell.ids_bound j hj; omega
  · have := base_injective e; omega

theorem selBody_away (divide : Bool) :
    base 2400∉wires (Q6EndpointCell.body divide base (base 2409) (base 2410)) := fun h =>
  selW0_away (Q6EndpointCell.body_support divide base (base 2409) (base 2410) selW0
    Finset.subset_union_left (Finset.mem_union_right _ (Finset.mem_singleton_self _)) h)

theorem selHalf_away (divide : Bool) : base 2400∉wires (Q6EndpointCell.half divide base (base 2409)) :=
  fun h => selW0_away (Q6EndpointCell.half_support divide base (base 2409) selW0
    Finset.subset_union_left h)

theorem selHalfE_away (divide : Bool) : base 2400∉wires (Q6EndpointCell.halfE divide base (base 2409)) :=
  fun h => selHalf_away divide (Q6EndpointCell.halfE_wires divide _ _ h)

theorem selSwap_away : base 2400∉wires swapBody := by
 have sub : wires swapBody⊆wires (Q6EndpointCell.body true base (base 2409) (base 2409)) := by
  simp only [swapBody,Q6EndpointCell.body,if_true,wires_append,Q6EndpointCell.ports_r,
    Q6EndpointCell.ports_y]
  exact Finset.subset_union_right
 have flag : base 2409∈selW0 := by simp [selW0]
 exact fun h => selW0_away (Q6EndpointCell.body_support true base (base 2409) (base 2409)
   selW0 Finset.subset_union_left flag (sub h))

theorem selSwapM_away : base 2400∉wires swapBodyM := by
  rw [swapBodyM,UncompSwap.mswap_wires]
  exact selSwap_away

theorem selHist_away (start : Nat) (hs : start+5 ≤ 512) :
    base 2400∉wires (NewHistory5.encode base start) ∧ base 2400∉wires (NewHistory5.decode base start) := by
  have lift (P : Program) (he : P=NewHistory5.encode base start ∨ P=NewHistory5.decode base start) :
      base 2400∉wires P := by
    intro hq
    obtain ⟨u,hu⟩ := NewHistory5.history_gate_mem base start P he _ hq
    have bound := NewHistory5.historyId_bound start hs u
    have hu' : base 2400=base (History5.historyId start u) := hu
    have := base_injective hu'
    omega
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

theorem selCenter_away : base 2400∉wires HalfFieldOB5.centerT ∧
    base 2400∉wires HalfFieldOB5.canonT ∧ base 2400∉wires HalfFieldOB5.copyN := by
  have ids (q : Wire) (hq : q∈(HalfField.ids.map base).toFinset) : q≠base 2400 := by
    intro e
    subst e
    obtain ⟨i,hi,e⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have := base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,
      or_false] at hi
    omega
  have ren (P : Program) (hP : wires P⊆(HalfField.ids.map base).toFinset) :
      base 2400∉wires (renameProgram HalfFieldOB5.endpointMap P) := by
    rw [renameProgram_support]
    intro h
    obtain ⟨q,hq,e⟩ := Finset.mem_image.mp h
    rw [← selEndpoint_fix] at e
    exact ids q (hP hq) (HalfFieldOB5.endpointMap.injective e)
  exact ⟨ren _ HalfField.centerT_sites,ren _ HalfField.canonT_sites,
    fun h => ids _ (HalfField.copyN_sites h) rfl⟩

theorem selInt_away : base 2400∉wires (stackForwardT) ∧ base 2400∉wires (stackReverseT) := by
  have bad : base 2400∉OB5.integerSites := by
    intro h
    obtain ⟨l,e,hl⟩ := (OB5.integerSites_mem _).mp h
    have := base_injective e
    omega
  exact ⟨fun h => bad (StackOB5.forward_support (stackForwardT_subset h)),fun h => bad (StackOB5.reverse_support (stackReverseT_subset h))⟩

theorem selPrefix_away : base 2400∉(NativeFirstDirect.prefixSites base).toFinset := by
  intro h
  simp only [NativeFirstDirect.prefixSites,wireBlock,List.mem_toFinset,List.mem_append,
    List.mem_cons,List.mem_map,List.mem_range'_1,List.not_mem_nil,or_false,
    base_injective.eq_iff] at h
  omega

theorem selClear_away : base 2400∉wires (skywalkArithmeticClear base) := by
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires]
  simp [base]

/-! ### Letters -/

theorem selLetter_nodup (i : Nat) (hi : i < 510) :
    [base 2400,(tapeLetter i).1.1,base 2409].Nodup ∧ [base 2400,(tapeLetter i).1.2,base 2409].Nodup := by
  simp only [tapeLetter]
  rw [mixedTape_base_getD i (by omega)]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true,
    not_or,not_false_eq_true,base_injective.eq_iff]
  omega

theorem selLetters_nodup (j : Nat) (hj : j < 102) (l : MixedTranscriptLetter)
    (hl : l∈Replay5.letters j) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have := List.mem_range.mp hk
  exact selLetter_nodup (5*j+k) (by omega)

theorem selRest_nodup (l : MixedTranscriptLetter) (hl : l∈Replay5.restLetters) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have := List.mem_range'_1.mp hk
  exact selLetter_nodup k (by omega)

/-! ### Cells and packets -/

theorem selCell_sel (divide : Bool) (g sw : Wire) (ig is : Bool)
 (hg : [base 2400,g,base 2409].Nodup) (hs : [base 2400,sw,base 2409].Nodup) :
 Sel (base 2400) 2 (cellS divide g sw)
   (OneFlagCell.cell divide base (base 2400) g sw (base 2409) ig is) := by
 have swap := ((Sel.refl _ _ selSwap_away).window sw (base 2409) is hs)
 have half (d : Bool) := ((Sel.refl _ _ (selHalf_away d)).window g (base 2409) ig hg)
 cases divide
 · simpa only [cellS,OneFlagCell.cell,OneFlagCell.halfWindow,OneFlagCell.selectSwap,
     swapBody,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,if_false] using
     (swap.append (half false)).cast (by norm_num) rfl rfl
 · simpa only [cellS,OneFlagCell.cell,OneFlagCell.halfWindow,OneFlagCell.selectSwap,
     swapBody,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,if_true] using
     ((half true).append swap).cast (by norm_num) rfl rfl

theorem selRaw_sel (divide : Bool) (ls : List MixedTranscriptLetter)
    (hl : ∀ l∈ls, [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup) :
    Sel (base 2400) (2*ls.length) (rawReplayS divide ls) (FrontierReplay1591.rawReplay divide ls) := by
  induction ls with
  | nil => exact (Sel.refl _ [] (by simp [wires])).cast (by simp) rfl rfl
  | cons l ls ih =>
    have hh := hl l (List.mem_cons_self ..)
    have rest := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    cases divide
    · exact (rest.append (selCell_sel false l.1.1 l.1.2 l.2.1 l.2.2 hh.1 hh.2)).cast
        (by simp only [List.length_cons]; omega) rfl rfl
    · exact ((selCell_sel true l.1.1 l.1.2 l.2.1 l.2.2 hh.1 hh.2).append rest).cast
        (by simp only [List.length_cons]; omega) rfl rfl

theorem selPacket_sel (divide : Bool) (j : Nat) (hj : j < 102) :
    Sel (base 2400) 10 (packetS divide j) (FrontierReplay1591.packet divide j) := by
  have codec := selHist_away (5*j) (by omega)
  have r := selRaw_sel divide (Replay5.letters j) (selLetters_nodup j hj)
  have len : (Replay5.letters j).length=5 := by simp [Replay5.letters]
  rw [len] at r
  have b : Sel (base 2400) 10 (basePacketS divide j) (FrontierReplay1591.basePacket divide j) :=
    (((Sel.refl _ _ codec.2).append r).append (Sel.refl _ _ codec.1)).cast (by norm_num) rfl rfl
  exact b.rename (shifted (Placement5.pi j)) (selShift_fix j hj)

theorem selGroups_sel (divide : Bool) (j n : Nat) (bound : j+n ≤ 102) :
    Sel (base 2400) (10*n) (groupsS divide j n) (FrontierReplay1591.groups divide j n) := by
  unfold groupsS FrontierReplay1591.groups
  induction n generalizing j with
  | zero => exact (Sel.refl _ [] (by simp [wires])).cast (by simp) rfl rfl
  | succ n ih =>
    have head := selPacket_sel divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide
    · simp only [PacketSequence.program,Bool.false_eq_true,if_false]
      exact (rest.append head).cast (by ring) rfl rfl
    · simp only [PacketSequence.program,if_true]
      exact (head.append rest).cast (by ring) rfl rfl

theorem selFirstSwap_sel : Sel (base 2400) 1 firstSwapS FrontierReplay1591.firstSwap := by
  have n : [base 2400,base 1028,base 2409].Nodup := by decide
  exact ((Sel.refl _ _ selSwap_away).window (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 n).cast (by norm_num) rfl rfl

theorem selFirstSwapM_sel : Sel (base 2400) 1 firstSwapMS FrontierReplay1591.firstSwapM := by
  have n : [base 2400,base 1028,base 2409].Nodup := by decide
  exact ((Sel.refl _ _ selSwapM_away).window (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 n).cast (by norm_num) rfl rfl

theorem selFirstPacket_sel (divide : Bool) :
    Sel (base 2400) 9 (firstPacketS divide) (FrontierReplay1591.firstPacket divide) := by
  have codec := selHist_away 0 (by omega)
  have r := selRaw_sel divide Replay5.restLetters selRest_nodup
  have len : Replay5.restLetters.length=4 := by simp [Replay5.restLetters]
  rw [len] at r
  have body : Sel (base 2400) 9 (firstBodyS divide) (FrontierReplay1591.firstBody divide) := by
    cases divide
    · exact (r.append selFirstSwapM_sel).cast (by norm_num) rfl rfl
    · exact (selFirstSwap_sel.append r).cast (by norm_num) rfl rfl
  have b : Sel (base 2400) 9 (baseFirstPacketS divide) (FrontierReplay1591.baseFirstPacket divide) :=
    (((Sel.refl _ _ codec.2).append body).append (Sel.refl _ _ codec.1)).cast (by norm_num) rfl rfl
  exact b.rename (shifted (Placement5.pi 0)) (selShift_fix 0 (by omega))

theorem selEnd_sel (divide : Bool) :
    Sel (base 2400) 1 (endPacketS divide) (FrontierReplay1591.endPacket divide) := by
  have n : [base 2400,base 510,base 2409].Nodup := by decide
  have b : Sel (base 2400) 1 (rawEndS divide) (FrontierReplay1591.rawEnd divide) :=
    ((Sel.refl _ _ (selHalfE_away divide)).window (base 510) (base 2409)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1 n).cast (by norm_num) rfl rfl
  exact b.rename (shifted Placement5.pi0) selShift0_fix

/-! ### Replay, segment, kernel -/

theorem selLogical_sel (divide : Bool) :
    Sel (base 2400) 1020 (logicalReplayS divide) (FrontierReplay1591.logicalReplay divide) := by
  have g := selGroups_sel divide 1 101 (by omega)
  have e := selEnd_sel divide
  have f := selFirstPacket_sel divide
  cases divide
  · exact ((e.append g).append f).cast (by norm_num) rfl rfl
  · exact ((f.append g).append e).cast (by norm_num) rfl rfl

theorem selReplay_sel (divide : Bool) :
    Sel (base 2400) 1020 (replayS divide) (FrontierReplay1591.replay divide) :=
  ((selLogical_sel divide).rename_inj (OB5.sig 511) (OB5.sig_injective 511 (by decide))).castb
    selSig_2400

end ECDSAAdd.Entrant.FrontierSW1591
