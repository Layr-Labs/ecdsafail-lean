import ECDSAAdd.Submission.Entrant.PrizeTail05e06b1e9
import ECDSAAdd.Submission.Entrant.PrizeTail8dd9f9e60

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 ArchiveStockSuffix StairConcreteAssembly Stair44Outer StockArchiveBanks StairV3Primitives StairPhysicalPhase
def free (q:Wire):Bool:=!(61302683078834518773225434680755157133632473222803583166596865976506739040523029895568267513251196792255204421816894308665018709045412178787043866194374854402116604136946129557206849924814154841423225785080261095258402746558605655416811190073246751535938248821978026700862730755112073080035491379749313447083789981560973892543876236738983888389161431165519159945917280487862863784285493860179091287828670740342624836436117264721656561406160920366751127682473174734414479748713767964582368296841664508966614364077388242087195085776492157470769152:Nat).testBit q
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
theorem occupied:∀(b:Bank)(i:Fin 16),free (siteAt b i)=false:=by decide +kernel
def check (P:Program):Bool:=StairWireCheck.allSites free P
theorem checked {P:Program} (h:check P=true):∀q∈archives,q∉wires P:=by
  intro q hq used
  obtain ⟨b,j,rfl⟩:=StockPlacedWindow.bank_rep q hq
  have safe:=StairWireCheck.allSites_sound free P h _ used
  rw [occupied] at safe
  contradiction
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitFrame
open Arithmetic MappedCompressed Secp256k1 StairField13V3 StairField13V3Clean
open StairConcreteAssembly StairField2V3Replay StairField2V3Delta StairField2V3Couple
open StairField2V3ExitPlanR StairField2V3LastRecX StairPhysicalLayout StairOuterPlacement
open StairLoanExitReachX
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run wires renameProgram

def stockPrefix (k : Nat) : Program := (((exitPieces cp hostPlan k).take 21).map Piece.H).flatten

def Pinned (x : Nat) (ref : State) : Prop := ∃ record, FrameAt x 85 record ∧ AgreeOutside (Δv 87) ref record
def Loan (ref : State) : Prop := ∀q ∈ StairSchedule.exclusiveRoles ++ hosts 87, ref.basis (fieldPlace q) = false

private theorem ofMiddle (k x : Nat) (u : State) (hu : ExitMiddleX k x u) (m : List Bool) :
    Pinned x (run XS21 m u) := by
  obtain ⟨Q, link⟩ := rch21 k x (StairOpenWiring.exitPlans k x) StairOpenWiring.half760
  obtain ⟨old,rel,reachable⟩ := link u u ⟨hu,rfl⟩ m
  exact ⟨_,WindowFieldView.exitFrame 85 x _
    (StairField2V3ExitRec.reach_YE k x _ (reachX_E StairOpenWiring.half760 k x _ reachable)),rel.1⟩

private theorem logicalPinned (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    Pinned F.x (run (cut (xps k) 21) m s) := by
  rw [xcut21,run_append]
  exact ofMiddle k F.x _ ⟨s,F,rfl,_,rfl⟩ _

private theorem loanSite (q : Wire) (hq : q∈StairSchedule.exclusiveRoles ++ hosts 87) :
    fieldPlace q ∈ ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap) := by
  rw [hp_group false 0 1 84 (by decide)]
  exact List.mem_map.mpr ⟨q,hq,rfl⟩

private theorem fullCutClean (k : Nat) (parts : StairField13V3Fresh.ExitClean k) :
    CutClean (ExitPre k) (cut (xps k) 21) ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap) :=
  parts.groupsBefore (21,0,1,84) (by simp)

private theorem cutLoan {P : Program} {pre : State → Prop}
    (clean : CutClean pre P ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap))
    (s : State) (h : pre s) (m : List Bool) : Loan (run P m s) := by
  intro q hq
  exact clean s h m _ (loanSite q hq)

private theorem logicalLoan (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    Loan (run (cut (xps k) 21) m s) :=
  cutLoan (fullCutClean k (exitClean_of_planR StairOpenWiring.exitPlans StairOpenWiring.half760 k)) s ⟨F⟩ m

theorem at_cut (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    Pinned F.x (run (stockPrefix k) m s) ∧ Loan (run (stockPrefix k) m s) := by
  have eq := Stair44HostedCut.exit k 21 s ⟨F⟩ m
  change run (stockPrefix k) m s = run (cut (xps k) 21) m s at eq
  rw [eq]
  exact ⟨logicalPinned k F m,logicalLoan k F m⟩

theorem tag (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    (run (stockPrefix k) m s).basis (fieldPlace (base 720)) = false :=
  (at_cut k F m).2 _ (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.WindowExitFrame

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 ArchiveStockSuffix StairConcreteAssembly Stair44Outer StockArchiveBanks
open StairV3Primitives StairPhysicalPhase StairPhysicalLayout
set_option maxRecDepth 80000
set_option maxHeartbeats 6000000
attribute [local irreducible] wires
def Clear (P:Program):Prop:=∀q∈archives,q∉wires P
theorem both {A B:Program} (a:Clear A) (b:Clear B):Clear (A++B):=by
  intro q h
  rw [wires_append,Finset.mem_union]
  exact fun hit=>hit.elim (a q h) (b q h)
private theorem rows87 {P:Program} (sub:∀q∈wires P,q∈StairPhysicalPrimitives.rowSitesL 87):
    Clear (renameProgram phaseRelabel P):=by
  have rowFree:∀q∈StairPhysicalPrimitives.rowSitesL 87,free (phaseRelabel q)=true:=by decide +kernel
  intro q h used
  obtain ⟨b,i,rfl⟩:=StockPlacedWindow.bank_rep _ h
  rw [renameProgram_support] at used
  obtain ⟨w,hw,eq⟩:=Finset.mem_image.mp used
  have ok:=rowFree w (sub w hw)
  rw [eq,occupied] at ok
  contradiction
private theorem orientOK:Clear (renameProgram xRelabel (StairV3Primitives.orient 425)):=checked (by decide +kernel)
private theorem packetOK:Clear (renameProgram (OB5.sig 425) (Rolling1588.Integer.packFirst base true 425)):=checked (by decide +kernel)
private theorem unpacketOK:Clear (renameProgram (OB5.sig 425) (Rolling1588.unpackAtTick true 425)):=checked (by decide +kernel)
private theorem moveOK:Clear (phaseBMove):=checked (by decide +kernel)
private theorem restoreOK:Clear (phaseBReturn):=checked (by decide +kernel)
theorem firstPack_free:Clear checkpointPrimitives.firstPack:=by
  exact both (both (both orientOK packetOK) moveOK) (rows87 (StairPhysicalPrimitives.pack_rows 87 (by decide)))
theorem firstUnpack_free:Clear checkpointPrimitives.firstUnpack:=by
  exact both (both (both (rows87 (StairPhysicalPrimitives.unpack_rows 87 (by decide))) restoreOK) unpacketOK) orientOK
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitPieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairHostsSchedule ExteriorPorts
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires

def beforeParity := StairSchedule.hostedX ++ StairSchedule.fieldRename (exitLowPrefix hostPlan)
def beforeGroup := StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram ++
  StairSchedule.fieldRename (renameProgram Prefix1590.borrow
    (StairSchedule.reverseLast cp ++ hostedGroup hostPlan false 42 98 2 ++
    StairSchedule.reverseSegment cp 22 12 490 500 ++ hostedGroup hostPlan false 37 96 2 ++
    StairSchedule.reverseSegment cp 32 22 480 490 ++ hostedGroup hostPlan false 31 93 3 ++
    StairSchedule.reverseSegment cp 47 32 465 480 ++ hostedGroup hostPlan false 23 90 3 ++
    StairSchedule.reverseSegment cp 62 47 450 465 ++ hostedGroup hostPlan false 14 85 5 ++
    StairSchedule.reverseSegment cp 87 62 425 450))
def afterGroup := StairSchedule.fieldRename (FourScratchWindow.unprefix ++
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false) (Rolling1588.placedFirstPacket false))
def leading (setup : Program) := setup ++ beforeParity ++ setup ++ beforeGroup
def field (setup group : Program) := leading setup ++ renameProgram fieldEquiv group ++ afterGroup

theorem ordinary : StairHostsSchedule.exitFieldHosted cp hostPlan =
    field StairSchedule.paritySetup (WindowFieldCosts.group false 1 84) := by
  simp only [field,leading,beforeParity,beforeGroup,afterGroup,StairHostsSchedule.exitFieldHosted,
    exitLowSuffix,exitHeadSuffix,WindowFieldCosts.group,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem corrected : WindowParityCaller.exitFieldHosted cp =
    field WindowFieldParity.setup (WindowFieldCosts.group84 false) := by
  simp only [field,leading,beforeParity,beforeGroup,afterGroup,WindowParityCaller.exitFieldHosted,
    WindowCallerCosts.exitLowSuffix,WindowCallerCosts.exitHeadSuffix,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem prefix_shape (k : Nat) : WindowExitFrame.stockPrefix k =
    exitReferenceOpening ++ leading StairSchedule.paritySetup := by
  simp only [WindowExitFrame.stockPrefix,leading,beforeParity,beforeGroup,exitPieces,List.take_succ_cons,
    List.take_zero,groupSlot,lowCommon,common,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil,exitReferenceOpening,exitLowPrefix,exitHeadPrefix,
    hostedEndpoint,fieldRename_append,rename_append,List.append_assoc]

theorem cutAfter (k : Nat) {s : State} (F : ExitFrame k s) (m n : List Bool) :
    let ref := run (leading StairSchedule.paritySetup) n (run exitReferenceOpening m s)
    WindowExitFrame.Pinned F.x ref ∧ WindowExitFrame.Loan ref := by
  have h := WindowExitFrame.at_cut k F (WindowFieldJourney.joinTapes exitReferenceOpening m n)
  rwa [prefix_shape,WindowFieldJourney.joined] at h

theorem hostedGroup (x : Nat) (a r : State) (m : List Bool)
    (rows : StockArchiveBanks.Bank → Nat)
    (labels : ∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (StockArchiveBanks.tick b) x p (rows b))
    (initial : WindowFieldMask.Fits (fieldRows rows) (WindowFieldJourney.initialCode false) a r)
    (pinned : WindowExitFrame.Pinned x r) (loan : WindowExitFrame.Loan r) :
    WindowFieldMask.Fits (fieldRows rows)
      (WindowFieldJourney.finalCode false (WindowFieldJourney.plan false) (WindowFieldJourney.initialCode false))
      (run (renameProgram fieldEquiv (WindowFieldCosts.group84 false)) m a)
      (run (renameProgram fieldEquiv (WindowFieldCosts.group false 1 84))
        (WindowFieldJourney.referenceTape false (WindowFieldJourney.plan false) m) r) := by
  obtain ⟨record,pin,agreement⟩ := pinned
  have ids : ∀j∈WindowFieldMask.bankIds,fieldRows rows j<63145 := by
    intro j hj
    obtain ⟨b,rfl⟩ := idAt j hj
    rw [rowsAt]
    exact (labels b).1
  have chronological : ∀j∈WindowFieldMask.bankIds, ArchiveStockRows.Chronology (5*j-5) x p (fieldRows rows j) := by
    intro j hj
    obtain ⟨b,rfl⟩ := idAt j hj
    rw [rowsAt]
    have times : ∀k : StockArchiveBanks.Bank, 5*groupId k-5=StockArchiveBanks.tick k := by decide +kernel
    rw [times]
    exact (labels b).2
  apply hosted
  exact WindowFieldView.caller false x (fieldRows rows) ids chronological (pullState fieldEquiv a) r record m
    (fitsPull fieldEquiv fieldEquiv.injective fieldFix initial) pin agreement
    (loan _ (by decide +kernel)) loan
end ECDSAAdd.Entrant.StairPacket.WindowExitPieces

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 35000
theorem clearSafe:Clear (FourScratchWindow.clearProgram):=checked (by decide +kernel)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 35000
theorem unprefixSafe:Clear (FourScratchWindow.unprefix):=checked (by decide +kernel)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5 StairConcreteAssembly Stair44Outer
set_option maxRecDepth 80000
set_option maxHeartbeats 6000000
private theorem wipeOK:Clear (skywalkArithmeticClear base):=checked (by decide +kernel)
private theorem tickOK:Clear (renameProgram (sig 511) tickR):=checked (by decide +kernel)
private theorem lastBackOK:Clear (renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)):=checked (by decide +kernel)
private theorem mergedOK:Clear (Six505.merged6):=checked (by decide +kernel)
private theorem packedOK:Clear (Six505.packP false):=checked (by decide +kernel)
private theorem afterOK:Clear (ForwardSixPlacement.after false):=checked (by decide +kernel)
theorem reverseEnd_free:Clear reverseEnd:=both (both wipeOK tickOK) lastBackOK
theorem forwardEnd_free:Clear forwardEnd:=both (both (both mergedOK packedOK) afterOK) wipeOK
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks ArchiveStockSuffix StairOuterPlacement
theorem mapped {P:Program} (f:Wire→Wire) (inj:Function.Injective f) (fix:Fixed f) (clear:Clear P):Clear (renameProgram f P):=by
  intro q hit used
  rw [renameProgram_support] at used
  obtain ⟨v,use,eq⟩:=Finset.mem_image.mp used
  obtain ⟨b,i,rfl⟩:=StockPlacedWindow.bank_rep q hit
  have same:=inj (eq.trans (fix b i).symm)
  exact clear _ ((chart b i).2.2.2) (same ▸ use)
theorem fieldMapped {P:Program} (c:Clear P):Clear (renameProgram fieldEquiv P):=mapped _ fieldEquiv.injective fieldFix c
def noBorrow:Equiv.Perm Wire:=⟨fun q=>Equiv.swap FrontierEntry1591Field.work FrontierEntry1591Field.host (HostOB5.hostSwap q),
  fun q=>HostOB5.hostSwap (Equiv.swap FrontierEntry1591Field.work FrontierEntry1591Field.host q),
  fun q=>by simp only [Equiv.swap_apply_self,HostOB5.hostSwap_invol],fun q=>by simp only [HostOB5.hostSwap_invol,Equiv.swap_apply_self]⟩
theorem noBorrowFixed:Fixed noBorrow:=by unfold Fixed;decide +kernel
theorem fieldRename_free {P:Program} (c:Clear P):Clear (StairSchedule.fieldRename P):=by
  unfold StairSchedule.fieldRename StairSchedule.parityRename
  rw [renameProgram_comp]
  exact mapped _ noBorrow.injective noBorrowFixed c
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StockArchiveBanks ArchiveStockSuffix StairPhysicalLayout StairPhysicalPrimitives
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
theorem live_rows (B:Nat) (h:B∈budgets):∀q∈rowSitesL B,free q=true:=by
  have ok:budgets.all (fun b=>(rowSitesL b).all free)=true:=by decide +kernel
  exact List.all_eq_true.mp (List.all_eq_true.mp ok B h)
theorem of_rows {B:Nat} (h:B∈budgets) {P:Program} (sub:∀q∈wires P,q∈rowSitesL B):Clear P:=by
  intro q hit used
  obtain ⟨b,i,rfl⟩:=StockPlacedWindow.bank_rep q hit
  have pass:=live_rows B h _ (sub _ used)
  rw [occupied] at pass
  contradiction
theorem packFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.pack B):=of_rows h (pack_rows B h)
theorem unpackFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.unpack B):=of_rows h (unpack_rows B h)
theorem tfFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.tickForward (startFor B)):=of_rows h (tickForward_rows B h)
theorem trFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.tickReverse (startFor B)):=of_rows h (tickReverse_rows B h)
theorem mfFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.middleForward (startFor B+1) (endFor B-startFor B-1)):=of_rows h (middleForward_rows B h)
theorem mrFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.middleReverse (startFor B+1) (StairPhysicalPrimitivesFix505.reverseEnd B-startFor B-1)):=
  of_rows h (StairPhysicalPrimitivesFix505.middleReverseFix_rows B h)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 ArchiveStockSuffix StockArchiveBanks StairArchiveInactive
open StairConcreteAssembly StairHostsSchedule StairPhysicalLayout StairLoanGroupSupport
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] wires renameProgram
def src (j:Nat) (b:Bank) (i:Fin 16):Wire:=(shifted (Placement5.pi j)).symm (OB5.sig 511 (siteAt b i))
private def past (q:Wire):Bool:=(126775176741748199005298032430817139045996731504449590227065959312526702177895107081230742342186766337435368052184766223088207704535346555108244967147894096960274009854312594099977521169993731686437146757106014421157568970380655112189389352141636812520406750021906729034961291325109341097198791953274681460510316346301923188344784208621023417820078625386117310233475084937028551998884672387940352:Nat).testBit q
private theorem fixedSources:∀j∈List.range' 85 17,∀(b:Bank)(i:Fin 16),src j b i=src 85 b i:=by decide +kernel
private theorem tagged:∀(b:Bank)(i:Fin 16),past (src 85 b i)=true:=by decide +kernel
private theorem globals:∀q∈[base 2400,base 2409,base 2410]++Q6EndpointCell.ids.map base,past q=false:=by decide +kernel
private theorem recent:∀j∈List.range' 85 17,∀i:Fin 10,past (History5.historyMap base (5*j) i)=false:=by decide +kernel
private theorem miss (j:Nat) (hj:j∈List.range' 85 17) (b:Bank) (i:Fin 16):src j b i∉cover j:=by
  intro hit
  have yes:=tagged b i
  rw [←fixedSources j hj b i] at yes
  rcases List.mem_append.mp hit with g|hist
  · rw [globals _ g] at yes;contradiction
  · obtain ⟨k,_,eq⟩:=List.mem_map.mp hist
    rw [←eq,recent j hj k] at yes;contradiction

private theorem packetFree (d:Bool) (j:Nat) (lo:85≤j) (hi:j<102):Clear (renameProgram (OB5.sig 511) (Rolling1588.packet d j)):=by
  intro q hit use
  obtain ⟨b,i,rfl⟩:=StockPlacedWindow.bank_rep q hit
  rw [renameProgram_support] at use
  obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp use
  rw [Rolling1588.packet,renameProgram_support] at hv
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
  have geom:src j b i=w:=by simp only [src,←eq,OB5.sig_invol 511 (by decide),Equiv.symm_apply_apply]
  apply miss j (List.mem_range'_1.mpr (by omega)) b i
  rw [geom]
  exact cover_read j (Rolling1588.basePacket_readSites_support d j hi hw)

private theorem regular (d:Bool) (j n:Nat) (lo:85≤j) (hi:j+n≤102):Clear (renameProgram (OB5.sig 511) (Rolling1588.groups d j n)):=by
  induction n generalizing j with
  | zero=>intro q _;simp [Rolling1588.groups,PacketSequence.program,renameProgram,wires]
  | succ n ih=>
    have a:=packetFree d j lo (by omega)
    have b:=ih (j+1) (by omega) (by omega)
    cases d <;> simp only [Rolling1588.groups,PacketSequence.program,if_true,if_false,Bool.false_eq_true,Six505.rename_append]
    · exact both b a
    · exact both a b

theorem groups (d:Bool) (k j n:Nat) (lo:85≤j) (hi:j+n≤102) (dk:k≤68)
    (safe:∀q∈hostPlan.group d k j n,free q=true):Clear (hostedGroup hostPlan d k j n):=by
  have roles:∀q∈StairSchedule.exclusiveRoles,free q=true:=by decide +kernel
  intro q hit used
  obtain ⟨b,i,rfl⟩:=StockPlacedWindow.bank_rep q hit
  obtain host|role|inner:=StairWireCheck.rebindMany_support _ _ _ _ used
  · have ok:=safe _ host;rw [occupied] at ok;contradiction
  · have ok:=roles _ (List.mem_of_mem_drop role);rw [occupied] at ok;contradiction
  · exact regular d j n lo hi _ ((chart b i).2.2.2) (placedGroups_sub d k dk j n inner)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment425Ori:Clear (checkpointPrimitives.orient 450):=checked (by decide +kernel)
private theorem segment425P:Clear (renameProgram (OB5.sig 450) (Rolling1588.Integer.packFirst base true 450)):=checked (by decide +kernel)
private theorem segment425U:Clear (renameProgram (OB5.sig 450) (Rolling1588.unpackAtTick true 450)):=checked (by decide +kernel)
theorem forward425:Clear (StairSchedule.forwardSegment checkpointPrimitives 87 62 425 450):=
  both (both (both (both (both (unpackFree 87 (by decide)) (tfFree 87 (by decide))) (mfFree 87 (by decide))) segment425Ori) segment425P) (packFree 62 (by decide))
theorem reverse425:Clear (StairSchedule.reverseSegment checkpointPrimitives 87 62 425 450):=
  both (both (both (both (both (unpackFree 62 (by decide)) segment425U) segment425Ori) (mrFree 87 (by decide))) (trFree 87 (by decide))) (packFree 87 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment450Ori:Clear (checkpointPrimitives.orient 465):=checked (by decide +kernel)
private theorem segment450P:Clear (renameProgram (OB5.sig 465) (Rolling1588.Integer.packFirst base true 465)):=checked (by decide +kernel)
private theorem segment450U:Clear (renameProgram (OB5.sig 465) (Rolling1588.unpackAtTick true 465)):=checked (by decide +kernel)
theorem forward450:Clear (StairSchedule.forwardSegment checkpointPrimitives 62 47 450 465):=
  both (both (both (both (both (unpackFree 62 (by decide)) (tfFree 62 (by decide))) (mfFree 62 (by decide))) segment450Ori) segment450P) (packFree 47 (by decide))
theorem reverse450:Clear (StairSchedule.reverseSegment checkpointPrimitives 62 47 450 465):=
  both (both (both (both (both (unpackFree 47 (by decide)) segment450U) segment450Ori) (mrFree 62 (by decide))) (trFree 62 (by decide))) (packFree 62 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment465Ori:Clear (checkpointPrimitives.orient 480):=checked (by decide +kernel)
private theorem segment465P:Clear (renameProgram (OB5.sig 480) (Rolling1588.Integer.packFirst base true 480)):=checked (by decide +kernel)
private theorem segment465U:Clear (renameProgram (OB5.sig 480) (Rolling1588.unpackAtTick true 480)):=checked (by decide +kernel)
theorem forward465:Clear (StairSchedule.forwardSegment checkpointPrimitives 47 32 465 480):=
  both (both (both (both (both (unpackFree 47 (by decide)) (tfFree 47 (by decide))) (mfFree 47 (by decide))) segment465Ori) segment465P) (packFree 32 (by decide))
theorem reverse465:Clear (StairSchedule.reverseSegment checkpointPrimitives 47 32 465 480):=
  both (both (both (both (both (unpackFree 32 (by decide)) segment465U) segment465Ori) (mrFree 47 (by decide))) (trFree 47 (by decide))) (packFree 47 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment480Ori:Clear (checkpointPrimitives.orient 490):=checked (by decide +kernel)
private theorem segment480P:Clear (renameProgram (OB5.sig 490) (Rolling1588.Integer.packFirst base true 490)):=checked (by decide +kernel)
private theorem segment480U:Clear (renameProgram (OB5.sig 490) (Rolling1588.unpackAtTick true 490)):=checked (by decide +kernel)
theorem forward480:Clear (StairSchedule.forwardSegment checkpointPrimitives 32 22 480 490):=
  both (both (both (both (both (unpackFree 32 (by decide)) (tfFree 32 (by decide))) (mfFree 32 (by decide))) segment480Ori) segment480P) (packFree 22 (by decide))
theorem reverse480:Clear (StairSchedule.reverseSegment checkpointPrimitives 32 22 480 490):=
  both (both (both (both (both (unpackFree 22 (by decide)) segment480U) segment480Ori) (mrFree 32 (by decide))) (trFree 32 (by decide))) (packFree 32 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment490Ori:Clear (checkpointPrimitives.orient 500):=checked (by decide +kernel)
private theorem segment490P:Clear (renameProgram (OB5.sig 500) (Rolling1588.Integer.packFirst base true 500)):=checked (by decide +kernel)
private theorem segment490U:Clear (renameProgram (OB5.sig 500) (Rolling1588.unpackAtTick true 500)):=checked (by decide +kernel)
theorem forward490:Clear (StairSchedule.forwardSegment checkpointPrimitives 22 12 490 500):=
  both (both (both (both (both (unpackFree 22 (by decide)) (tfFree 22 (by decide))) (mfFree 22 (by decide))) segment490Ori) segment490P) (packFree 12 (by decide))
theorem reverse490:Clear (StairSchedule.reverseSegment checkpointPrimitives 22 12 490 500):=
  both (both (both (both (both (unpackFree 12 (by decide)) segment490U) segment490Ori) (mrFree 22 (by decide))) (trFree 22 (by decide))) (packFree 22 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5 StairConcreteAssembly Stair44Outer
open StairPhysicalLayout StairTerminalV3
set_option maxRecDepth 80000
set_option maxHeartbeats 4800000
attribute [local irreducible] wires renameProgram
theorem terminalFixed:Fixed terminalPerm:=by unfold Fixed;decide +kernel
private theorem w:Clear (skywalkArithmeticClear base):=checked (by decide +kernel)
private theorem f:Clear Six505.merged6:=checked (by decide +kernel)
private theorem pk:Clear (Six505.packP true):=checked (by decide +kernel)
private theorem a:Clear (ForwardSixPlacement.after true):=checked (by decide +kernel)
private theorem t:Clear (renameProgram (sig 511) tickR):=checked (by decide +kernel)
private theorem k:Clear (renameProgram (sig 510) (Rolling1588.unpackAtTick true 510 ++ InverseFive23.candidate15)):=checked (by decide +kernel)
theorem forwardTerm:Clear checkpointPrimitives.forwardTerminal:=
  mapped _ terminalPerm.injective terminalFixed (both (both (both f pk) a) w)
theorem reverseTerm:Clear checkpointPrimitives.reverseTerminal:=
  mapped _ terminalPerm.injective terminalFixed (both w (both t k))
theorem forwardLast:Clear (StairSchedule.forwardLast checkpointPrimitives):=
  both (both (both (unpackFree 12 (by decide)) (tfFree 12 (by decide))) (mfFree 12 (by decide))) forwardTerm
theorem reverseLast:Clear (StairSchedule.reverseLast checkpointPrimitives):=
  both (both (both reverseTerm (mrFree 12 (by decide))) (trFree 12 (by decide))) (packFree 12 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitStages
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open StockArchiveBanks WindowStartStates WindowMiddlePieces ExteriorPorts WindowExitPieces
open WindowFieldMask WindowFieldJourney
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000
attribute [local irreducible] run measurementCount

def endF := renameProgram phaseHost Stair44Outer.forwardEnd
def unpack := renameProgram phaseHost checkpointPrimitives.firstUnpack
def beginW := opening false 234 ++ endF
def beginR := original false 234 ++ endF

theorem refBegin : beginR = Stair44Kernel.mulLead := by
  simp only [beginR,original,endF,Stair44Kernel.mulLead,Stair44Kernel.finishM,Stair44Outer.forwardEnd,Six505.rename_append,List.append_assoc]

theorem begin_pair (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    ∃n, Paired false F.x (run beginW m s) (run beginR n s) (StockRowVector.rows F.x p) := by
  let A := opening false 234
  let B := original false 234
  let t := m.drop (measurementCount A)
  refine ⟨joinTapes B m t,?_⟩
  rw [beginW,beginR,joined,run_append,run_take]
  apply pairUnpull phaseHost phaseFix
  rw [endF,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective]
  exact (WindowStartStates.multiplication k F m).through _ forwardEnd_free _

theorem begin_record (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    run beginR m s = run StairField2V3Replay.exitReferenceOpening m s := by
  rw [refBegin]
  exact WindowStockHead.leadM k F m

def newP := (beginW ++ WindowParityCaller.exitFieldHosted checkpointPrimitives) ++ unpack
def oldP := (beginR ++ StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan) ++ unpack

theorem newShape : WindowMiddleContract.mulHead = newP := by
  simp only [WindowMiddleContract.mulHead,WindowKernelPrograms.mulBefore,newP,beginW,opening,endF,unpack,
    Six505.rename_append,List.append_assoc]
theorem oldShape : WindowMiddleContract.oldMulHead = oldP := by
  rw [oldP,refBegin]
  rfl

end ECDSAAdd.Entrant.StairPacket.WindowExitStages

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem viaFree {P : Program} (touch : ∀q∈wires P,free q=true) : Clear P := by
  intro q h used
  obtain ⟨b,i,rfl⟩ := StockPlacedWindow.bank_rep q h
  exact Bool.noConfusion ((occupied b i).symm.trans (touch _ used))

end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitReplay
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open StockArchiveBanks WindowStartStates WindowMiddlePieces ExteriorPorts WindowExitPieces
open WindowFieldMask WindowFieldJourney WindowExitStages
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] run measurementCount wires

def leadingOK : Prop := ∀ (x : Nat) (rows : StockArchiveBanks.Bank → Nat) (a r : State) (m : List Bool),
  Paired false x a r rows → ∃n, Paired false x (run (leading WindowFieldParity.setup) m a)
    (run (leading StairSchedule.paritySetup) n r) rows

abbrev C0 := initialCode false
abbrev C1 := finalCode false (plan false) C0
def gW := renameProgram fieldEquiv (WindowFieldCosts.group84 false)
def gR := renameProgram fieldEquiv (WindowFieldCosts.group false 1 84)

def RStart (x : Nat) (rows : StockArchiveBanks.Bank → Nat) (s : State) (a r : State) : Prop :=
  Paired false x a r rows ∧ ∃m, r = run StairField2V3Replay.exitReferenceOpening m s
def RCut (x : Nat) (rows : StockArchiveBanks.Bank → Nat) (a r : State) : Prop :=
  Paired false x a r rows ∧ WindowExitFrame.Pinned x r ∧ WindowExitFrame.Loan r

private theorem beginRel (k : Nat) {s : State} (F : ExitFrame k s) :
    Relates beginW beginR (fun a r=>a=s ∧ r=s) (RStart F.x (StockRowVector.rows F.x p) s) := by
  rintro a r ⟨rfl,eq⟩ m
  subst r
  obtain ⟨n,rel⟩ := begin_pair k F m
  exact ⟨n,rel,n,begin_record k F n⟩

private theorem leadingRel (ok : leadingOK) (k : Nat) {s : State} (F : ExitFrame k s) (rows : StockArchiveBanks.Bank → Nat) :
    Relates (leading WindowFieldParity.setup) (leading StairSchedule.paritySetup)
      (RStart F.x rows s) (RCut F.x rows) := by
  rintro a r ⟨pair,u,rfl⟩ m
  obtain ⟨n,h⟩ := ok _ _ _ _ m pair
  exact ⟨n,h,cutAfter k F u n⟩

private theorem windowRel (x : Nat) (rows : StockArchiveBanks.Bank → Nat) :
    Relates gW gR (RCut x rows) (Fits (fieldRows rows) C1) := by
  rintro a r ⟨pair,pin,loan⟩ m
  exact ⟨_,hostedGroup x a r m rows pair.labels (fits pair) pin loan⟩

private theorem template (A P G T U : Program) :
    (A ++ ((P ++ G) ++ T)) ++ U = (((A ++ P) ++ G) ++ (T ++ U)) := by
  simp only [List.append_assoc]

private theorem newPath : WindowMiddleContract.mulHead =
    (((beginW ++ leading WindowFieldParity.setup) ++ gW) ++ (afterGroup ++ unpack)) := by
  rw [newShape,newP,corrected]
  exact template _ _ _ _ _
private theorem oldPath : WindowMiddleContract.oldMulHead =
    (((beginR ++ leading StairSchedule.paritySetup) ++ gR) ++ (afterGroup ++ unpack)) := by
  rw [oldShape,oldP,ordinary]
  exact template _ _ _ _ _

theorem exit (leadingLaw : leadingOK) (endClear : Clear (afterGroup ++ unpack)) : WindowMiddleContract.exit := by
  intro k s F m
  have keep := pass (rows:=fieldRows (StockRowVector.rows F.x p)) (cs:=C1) (P:=afterGroup ++ unpack) (fun q h=>endClear q (whole ▸ h))
  have total := compose (compose (compose (beginRel k F) (leadingRel leadingLaw k F _)) (windowRel _ _)) keep
  obtain ⟨n,out⟩ := total s s ⟨rfl,rfl⟩ m
  rw [←newPath,←oldPath] at out
  have paired := fitsPull phaseHost phaseHost.injective phaseFix out
  have native := WindowEndBytes.mul_native k F n
  exact ⟨n,pairFinished paired native.ids native.bytes⟩
end ECDSAAdd.Entrant.StairPacket.WindowExitReplay

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

private theorem convert {P Q : Program}
    (env : wires P ⊆ wires Q ∪ StairBoundaryLoan.converterHosts.toFinset)
    (rec : wires Q ⊆ StairBoundaryLoan.converterLayout760.wires.toFinset) : Clear P := by
  have ok : (StairBoundaryLoan.converterLayout760.wires ++ StairBoundaryLoan.converterHosts).all free=true := by decide +kernel
  apply viaFree
  intro q hq
  apply List.all_eq_true.mp ok
  rcases Finset.mem_union.mp (env hq) with l|r
  · exact List.mem_append_left _ (List.mem_toFinset.mp (rec l))
  · exact List.mem_append_right _ (List.mem_toFinset.mp r)

theorem canon : Clear StairConcrete.bestLoans.canon :=
  convert StairBoundaryLoan.canon760Loan_envelope (by
    rw [StairBoundaryLoan.canon760_eq]
    exact (HalfConvert.support _ StairBoundaryLoan.converterLayout760_facts.widths).2)
theorem center : Clear StairConcrete.bestLoans.center :=
  convert StairBoundaryLoan.center760Loan_envelope (by
    rw [StairBoundaryLoan.center760_eq]
    exact (HalfConvert.support _ StairBoundaryLoan.converterLayout760_facts.widths).1)

theorem copy : Clear HalfFieldOB5.copyN := checked (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem mulEndpoint : Clear (hostedEndpoint hostPlan false 68) := by
  have ok : StairSiteEasy.multEndL.all (fun q=>free (OB5.sig 511 q))=true := by decide +kernel
  apply viaFree
  intro q h
  have e : StairConcrete.bestLoans.endPacket false 68=StairEndpointLoan44.endPacket760Loan44 false := by
    simp only [StairConcrete.bestLoans,StairConcrete.endPacket,Bool.false_eq_true,if_false,if_true]
  rw [hostedEndpoint,StairSchedule.placedEndPacket,e,renameProgram_support] at h
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
  exact List.all_eq_true.mp ok q (StairSiteEasy.endPacket760_false_mem q (StairEndpointLoan44.endPacket760Loan44_support hq))

private def outward (q : Wire) := OB5.sig 511 (Equiv.swap (base 760) (base 717) (shifted Placement5.pi0 q))
private def inner (q : Wire) := Equiv.swap (base 719) (base 510) q

theorem divEndpoint : Clear (renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint) := by
  have ok : DecoderBiasReuse.fixedLayout.wires.all (fun q=>free (outward (inner q)))=true := by decide +kernel
  apply viaFree
  intro q h
  rw [renameProgram_support,StairConcrete.bestLoans_divEndpoint] at h
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
  unfold CompareDecoder.BoundaryLoan.endPacket760DivLoan at hy
  rw [renameProgram_support] at hy
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
  rw [renameProgram_support] at ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  rcases Finset.mem_union.mp (ControlLoan1589.loanWindow_support _ _ _ _ hb) with h|h
  · rw [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl <;> decide +kernel
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    rw [wires_append,Finset.mem_union] at hz
    rcases hz with hz|hz
    · exact List.all_eq_true.mp ok z (List.mem_toFinset.mp (CompareDecoder.support (CompareDecoder.BoundaryLoan.Inclusion.cellDecoderLoan_sub hz)))
    · have hc := (InverseEndpointWires.pad_facts 507 (base 512)).2.2.2.1 hz
      rw [Finset.mem_singleton] at hc
      rw [hc]
      decide +kernel

end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel StairWireCheck
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem firstNo : ∀(b : Bank)(i : Fin 16), fpSup (siteAt b i)=false := by decide +kernel
theorem noRole : ∀(b : Bank)(i : Fin 16), siteAt b i∉StairSchedule.exclusiveRoles := by decide +kernel
theorem noHost : ∀(b : Bank)(i : Fin 16), siteAt b i∉StairPhysicalLayout.hosts 87 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitClear
open Arithmetic MappedCompressed Secp256k1 Rolling1588Lifetime StairConcreteAssembly
open StockArchiveBanks WindowExitPieces WindowExitStages ExteriorPorts StairField13V3
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
attribute [local irreducible] wires run measurementCount

theorem renameClear (fn : Wire → Wire) (inj : Function.Injective fn) (fixed : Fixed fn) {P : Program}
    (clear : Clear P) : Clear (renameProgram fn P) := by
  intro q hq used
  rw [renameProgram_support] at used
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp used
  by_cases orig : r∈ArchiveStockSuffix.archives
  · exact clear r orig hr
  · exact archive_pre inj fixed r orig hq

theorem fieldClear {P : Program} (clear : Clear P) : Clear (StairSchedule.fieldRename P) := by
  rw [fieldRename_eq]
  exact renameClear fieldMap fieldMap_injective (by unfold Fixed; decide +kernel) clear

theorem after (f : Clear FourScratchWindow.unprefix)
    (g : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
        (Rolling1588.placedFirstPacket false))) : Clear (afterGroup ++ unpack) :=
  both (fieldClear (both f g)) (renameClear phaseHost phaseHost.injective phaseFix firstUnpack_free)

private theorem pass {d x rows P} (clear : Clear P) :
    Relates P P (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,pair.through P clear m⟩

private theorem parity {d x rows} : Relates WindowFieldParity.setup StairSchedule.paritySetup
    (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,WindowFieldParity.setup_through pair m m⟩

theorem leading (pre : Clear beforeParity) (next : Clear beforeGroup) : WindowExitReplay.leadingOK := by
  intro x rows a r m pair
  exact compose (compose (compose parity (pass pre)) parity) (pass next) a r pair m

theorem exit (a : Clear beforeParity) (b : Clear beforeGroup) (f : Clear FourScratchWindow.unprefix)
    (g : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
        (Rolling1588.placedFirstPacket false))) : WindowMiddleContract.exit :=
  WindowExitReplay.exit (leading a b) (after f g)
end ECDSAAdd.Entrant.StairPacket.WindowExitClear

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel StairWireCheck
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

private theorem table (d : Bool) : allSites fpSup (Rolling1588.placedFirstPacket d)=true := by
  cases d
  · exact passSup_false
  · exact passSup_true

private theorem exclude (q : Wire) (h : q∈ArchiveStockSuffix.archives) :
    q∉StairPhysicalLayout.hosts 87 ∧ q∉StairSchedule.exclusiveRoles ∧ fpSup q=false := by
  obtain ⟨b,i,rfl⟩ := StockPlacedWindow.bank_rep q h
  exact ⟨noHost b i,noRole b i,firstNo b i⟩

private theorem rebind {P : Program} (hs : List Wire) (eq : hs=StairPhysicalLayout.hosts 87)
    (ok : allSites fpSup P=true) : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles hs P) := by
  intro q h used
  have neg := exclude q h
  rcases rebindMany_support StairSchedule.exclusiveRoles hs P q used with host | role | orig
  · exact neg.1 (eq ▸ host)
  · exact neg.2.1 role
  · exact Bool.noConfusion (neg.2.2.symm.trans (allSites_sound fpSup P ok q orig))

theorem first (d : Bool) : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket d)
    (Rolling1588.placedFirstPacket d)) :=
  rebind (hostPlan.firstPacket d) rfl (table d)

end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem tail (other : Clear (hostedGroup hostPlan true 44 100 2)) : Clear (entryTailSuffix hostPlan) :=
  both (both (both other divEndpoint) copy) canon
theorem head (other : Clear (hostedGroup hostPlan false 44 100 2)) : Clear (exitHeadPrefix hostPlan) :=
  both (both (both center copy) mulEndpoint) other
end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitOuter
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts WindowExitPieces
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
attribute [local irreducible] wires

theorem hostedX : Clear StairSchedule.hostedX := checked (by decide +kernel)

theorem ordinaryGroup (d : Bool) (k j n : Nat) (start : 85≤j) (bound : j+n≤102) (budget : k≤68)
    (tab : (hostPlan.group d k j n).all free=true) : Clear (hostedGroup hostPlan d k j n) :=
  groups d k j n start bound budget (List.all_eq_true.mp tab)

theorem other (d : Bool) : Clear (hostedGroup hostPlan d 44 100 2) :=
  ordinaryGroup d 44 100 2 (by decide) (by decide) (by decide) (by cases d <;> decide +kernel)

theorem pre : Clear beforeParity := by
  apply both hostedX
  apply fieldRename_free
  apply both _ unprefixSafe
  apply both clearSafe
  -- The outer field placement is applied once more by the caller.
  exact WindowExitClear.renameClear Prefix1590.borrow Prefix1590.borrow.injective
    (by unfold Fixed; decide +kernel) (WindowExteriorFixed.head (other false))

theorem endPart : Clear (afterGroup ++ WindowExitStages.unpack) :=
  WindowExitClear.after unprefixSafe (WindowExteriorFixed.first false)
end ECDSAAdd.Entrant.StairPacket.WindowExitOuter

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitReady
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts WindowExitPieces WindowExitOuter
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem before : Clear beforeGroup := by
  apply both (both hostedX (fieldRename_free clearSafe))
  rw [placedShape]
  apply fieldMapped
  apply both _ reverse425
  apply both _ (ordinaryGroup false 14 85 5 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse450
  apply both _ (ordinaryGroup false 23 90 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse465
  apply both _ (ordinaryGroup false 31 93 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse480
  apply both _ (ordinaryGroup false 37 96 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse490
  apply both _ (ordinaryGroup false 42 98 2 (by decide) (by decide) (by decide) (by decide +kernel))
  exact reverseLast

theorem exit : WindowMiddleContract.exit :=
  WindowExitReplay.exit (WindowExitClear.leading pre before) endPart
end ECDSAAdd.Entrant.StairPacket.WindowExitReady

end

