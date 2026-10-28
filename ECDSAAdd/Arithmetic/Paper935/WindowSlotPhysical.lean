import ECDSAAdd.Arithmetic.Paper935.WindowSlot
import ECDSAAdd.Arithmetic.Paper935.WindowStepPhysical
import ECDSAAdd.Arithmetic.Paper935.BlockedPostPhysical

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps ECDSAAdd.RecordedQuantum

/-- The public post-layout's existing validity certifies both measured streams. -/
theorem WindowPostLayout.physical (P : WindowPostLayout) (hv : P.Valid) :
    GatePhysical P.program ∧ GatePhysical P.inverse := by
  have hn : [P.zf,P.frozen,P.fire,P.active].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    exact ⟨⟨hv.zfFrozen,hv.zfFire,hv.activeZf.symm⟩,
      ⟨hv.fireFrozen.symm,hv.activeFrozen.symm⟩,hv.activeFire.symm⟩
  exact BlockedPost.post_physical _ _ _ _ _ _ _ _ _ _ hv.probe hn hv.fireRecord hv.compare hv.remint

/-- Every post-stage address, including comparison and probe scratch. -/
def WindowPostLayout.ports (P : WindowPostLayout) : List Wire :=
  P.one::P.zf::P.frozen::P.fire::P.active::P.witness::
    (P.recordWires++BlockedZero.ports P.blocks++P.record.flatMap ZeroBit.wires)

theorem WindowPostLayout.support (P : WindowPostLayout) :
    wires P.program⊆P.ports.toFinset ∧ wires P.inverse⊆P.ports.toFinset :=
  ⟨BlockedPost.publicPost_support _ _ _ _ _ _ _ _ _ _,
    BlockedPost.inverse_support _ _ _ _ _ _ _ _ _ _⟩

/-- Tag preparation and its unmeasured reverse are ordinary legal gates. -/
theorem RoutedBankLayout.mintControls_physical (L : RoutedBankLayout) (frozen zsign : Wire)
    (hn : [zsign,L.glow,L.parity,L.q].Nodup) (hfa : frozen≠L.active) :
    GatePhysical (L.mintControls frozen zsign) ∧
    GatePhysical (L.mintControls frozen zsign).reverse := by
  have h := L.mintControls_proper frozen zsign hn hfa
  exact ⟨(physical_embed _).mp (physical_of_proper _ h),
    (physical_embed _).mp (physical_of_proper _ (properProgram_reverse _ h))⟩

theorem RoutedBankLayout.mintControls_support (L : RoutedBankLayout) (frozen zsign : Wire) :
    wires (L.mintControls frozen zsign)⊆[frozen,L.active,zsign,L.glow,L.parity,L.q].toFinset := by
  intro q hq
  simp [mintControls,mintActivity,branchTags,wires,Instr.wires] at hq ⊢
  tauto

/-- Static validity of the entire retired arithmetic, including reminting swap. -/
theorem RoutedBankLayout.retiredWindow_physical (L : RoutedBankLayout) (hv : L.Valid)
    (out : WindowBank) (w : RowWindow) (A C : Arena) (resize : Program)
    (hp : L.after.Planned out w A C resize) (zero z carry : List Wire)
    (hn : (L.active::L.q::(zero++z++carry)).Nodup) (frozen zsign : Wire)
    (htag : [zsign,L.glow,L.parity,L.q].Nodup) (hfa : frozen≠L.active)
    (hsecond : out.fv.second≠L.q) :
    GatePhysical (L.retiredWindow out frozen zsign resize zero z carry) ∧
    GatePhysical (L.retiredWindowInverse out frozen zsign resize zero z carry) := by
  have a := L.mintControls_physical frozen zsign htag hfa
  have b := L.windowStep_physical hv out w A C resize hp zero z carry hn
  have aq : L.active≠L.q := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have e : GatePhysical (eraseAnd L.active out.fv.second L.q) := by
    simp [eraseAnd,GatePhysical,PhysicalInstr]
  have m : GatePhysical [.CCX L.active out.fv.second L.q] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,aq,hsecond]
  simp only [retiredWindow,retiredWindowInverse,taggedWindow,taggedWindowInverse,gatePhysical_append]
  exact ⟨⟨⟨a.1,b.1⟩,e⟩,⟨m,⟨b.2,a.2⟩⟩⟩

/-- Compose concrete layout validity all the way through freeze/offset processing. -/
theorem RoutedBankLayout.windowSlot_physical (L : RoutedBankLayout) (hv : L.Valid)
    (out : WindowBank) (w : RowWindow) (A C : Arena) (resize : Program)
    (hp : L.after.Planned out w A C resize) (zero z carry : List Wire)
    (hn : (L.active::L.q::(zero++z++carry)).Nodup) (frozen zsign : Wire)
    (htag : [zsign,L.glow,L.parity,L.q].Nodup) (hfa : frozen≠L.active)
    (hsecond : out.fv.second≠L.q) (P : WindowPostLayout) (hvP : P.Valid) :
    GatePhysical (L.windowSlot out P frozen zsign resize zero z carry) ∧
    GatePhysical (L.windowSlotInverse out P frozen zsign resize zero z carry) := by
  have r := L.retiredWindow_physical hv out w A C resize hp zero z carry hn frozen zsign htag hfa hsecond
  simp only [windowSlot,windowSlotInverse,gatePhysical_append]
  exact ⟨⟨r.1,(P.physical hvP).1⟩,⟨(P.physical hvP).2,r.2⟩⟩

/-- Arena closure adds the actual control and swap-read addresses to step support. -/
theorem RoutedBankLayout.retiredWindow_support (L : RoutedBankLayout) (out : WindowBank)
    (frozen zsign : Wire) (resize : Program) (zero z carry : List Wire)
    (hstep : wires (L.windowStep resize zero z carry)⊆arenaWires ∧
      wires (L.windowStepInverse resize zero z carry)⊆arenaWires)
    (hctrl : [frozen,L.active,zsign,L.glow,L.parity,L.q,out.fv.second].toFinset⊆arenaWires) :
    wires (L.retiredWindow out frozen zsign resize zero z carry)⊆arenaWires ∧
    wires (L.retiredWindowInverse out frozen zsign resize zero z carry)⊆arenaWires := by
  have prep : wires (L.mintControls frozen zsign)⊆arenaWires :=
    (L.mintControls_support frozen zsign).trans (by
      intro q hq; apply hctrl
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
      tauto)
  have erase : wires (eraseAnd L.active out.fv.second L.q)⊆arenaWires := by
    intro q hq; apply hctrl
    simp [eraseAnd,wires,Instr.wires,correctionWires] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]; tauto
  have mint : wires [.CCX L.active out.fv.second L.q]⊆arenaWires := by
    intro q hq; apply hctrl
    simp [wires,Instr.wires] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]; tauto
  simp only [retiredWindow,retiredWindowInverse,taggedWindow,taggedWindowInverse,
    wires_append,wires_reverse,Finset.union_subset_iff]
  exact ⟨⟨⟨prep,hstep.1⟩,erase⟩,⟨mint,⟨hstep.2,prep⟩⟩⟩

/-- Full slot support in the arena, reusing addresses across all stages. -/
theorem RoutedBankLayout.windowSlot_support (L : RoutedBankLayout) (out : WindowBank)
    (P : WindowPostLayout) (frozen zsign : Wire) (resize : Program) (zero z carry : List Wire)
    (hretired : wires (L.retiredWindow out frozen zsign resize zero z carry)⊆arenaWires ∧
      wires (L.retiredWindowInverse out frozen zsign resize zero z carry)⊆arenaWires)
    (hpost : P.ports.toFinset⊆arenaWires) :
    wires (L.windowSlot out P frozen zsign resize zero z carry)⊆arenaWires ∧
    wires (L.windowSlotInverse out P frozen zsign resize zero z carry)⊆arenaWires := by
  simp only [windowSlot,windowSlotInverse,wires_append,Finset.union_subset_iff]
  exact ⟨⟨hretired.1,P.support.1.trans hpost⟩,⟨P.support.2.trans hpost,hretired.2⟩⟩

end ECDSAAdd.Arithmetic.Paper935
