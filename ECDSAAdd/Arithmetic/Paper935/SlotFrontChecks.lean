import ECDSAAdd.Arithmetic.Paper935.PublicSlotCompiler

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.RecordedQuantum

/-- Public address-only checks for the complete front stream. They inspect
no quantum input and contain no semantic or probability oracle. -/
def SlotFront.PhysicalChecks (P : SlotFront) (F : SlotRegisters) : Prop :=
  let L := P.layout
  1≤F.counter.length ∧
  (L.active::L.q::(P.zero++F.counter++P.carry)).Nodup ∧
  [F.counter.getLastD 0,L.glow,L.parity,L.q].Nodup ∧ F.frozen≠L.active ∧
  P.exitBank.fv.second≠L.q ∧
  (L.q::L.parity::L.u::L.k::(L.f.wires++(L.glow::(L.gmid++[L.gsign])))).toFinset⊆arenaWires ∧
  (L.q::L.parity::L.u::L.k::((L.vlow::(L.vmid++[L.vsign]))++L.gv.wires)).toFinset⊆arenaWires ∧
  (L.active::L.vlow::(L.vmid++[L.vsign])).toFinset⊆arenaWires ∧
  (L.active::L.q::(P.zero++F.counter++P.carry)).toFinset⊆arenaWires ∧
  [F.frozen,L.active,F.counter.getLastD 0,L.glow,L.parity,L.q,P.exitBank.fv.second].toFinset⊆arenaWires

instance (P : SlotFront) (F : SlotRegisters) : Decidable (P.PhysicalChecks F) := by
  unfold SlotFront.PhysicalChecks
  infer_instance

theorem SlotFront.Compiled.physical (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (h : P.Compiled A b addWidth exitWidth F)
    (checks : P.PhysicalChecks F) : GatePhysical (P.program F) ∧ GatePhysical (P.inverse F) := by
  rcases checks with ⟨hz,hn,htag,hfa,hsecond,_,_,_,_,_⟩
  have hc := h.layouts P A b addWidth exitWidth F hz
  have pad := (b.resize_resources P.addBank addWidth A P.addArena P.padding hc.1).1
  have padPhysical := (physical_embed _).mp (physical_of_proper _ pad)
  have inversePhysical := (physical_embed _).mp (physical_of_proper _ (properProgram_reverse _ pad))
  have core := P.layout.retiredWindow_physical hc.2.1 P.exitBank exitWidth P.addArena P.exitArena P.resizing
    hc.2.2.2.1 P.zero F.counter P.carry hn F.frozen (F.counter.getLastD 0) htag hfa hsecond
  simp only [SlotFront.program,SlotFront.inverse,gatePhysical_append]
  exact ⟨⟨padPhysical,core.1⟩,⟨core.2,inversePhysical⟩⟩

theorem SlotFront.Compiled.support (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (h : P.Compiled A b addWidth exitWidth F)
    (checks : P.PhysicalChecks F) : wires (P.program F)⊆arenaWires ∧ wires (P.inverse F)⊆arenaWires := by
  rcases checks with ⟨hz,_,_,_,_,h1,h2,h3,hcounter,hctrl⟩
  have hc := h.layouts P A b addWidth exitWidth F hz
  have pad := (b.resize_resources P.addBank addWidth A P.addArena P.padding hc.1).2.2.2
  have rows := P.layout.support hc.2.1 h1 h2 h3
  have step := P.layout.windowStep_support P.exitBank exitWidth P.addArena P.exitArena P.resizing hc.2.2.2.1
    P.zero F.counter P.carry rows.1 hcounter hc.2.2.2.2.1 hc.2.2.2.2.2.1
  have core := P.layout.retiredWindow_support P.exitBank F.frozen (F.counter.getLastD 0)
    P.resizing P.zero F.counter P.carry step hctrl
  simp only [SlotFront.program,SlotFront.inverse,wires_append,wires_reverse,Finset.union_subset_iff]
  exact ⟨⟨pad,core.1⟩,⟨core.2,pad⟩⟩

end ECDSAAdd.Arithmetic.Paper935
